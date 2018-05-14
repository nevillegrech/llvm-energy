#!/usr/bin/env python3
__doc__='''
Usage:
  inferCR.py  --option <bitcodefile>
  my_program [<optional-argument>]
  my_program --another-option=<with-argument>
  my_program (--either-that-option | <or-this-argument>)
  my_program <repeating-argument> <repeating-argument>...

'''
import sys
from llvm.core import *
from collections import defaultdict
from itertools import chain
from functools import reduce as fold
from math import pow
import json

llvmunit=14
inverse_op={'!=':'==','<=':'>','>=':'<','==':'!=','<':'>=','>':'<='}
binops='*%-+<=>='
class Solver:
    '''Base class for the solver.
    Important methods are addrel and solve.'''
    mapping={}
    def addrel(*args):
        '''Add a cost relation to the solver instance, has to be implemented'''
        raise NotImplementedError('')
    def solve(**args):
        '''Invokes solver with the cost relations that were passed'''
        raise NotImplementedError('')
    def codetostr(self,block):
        res=block.name.replace('.','').lower().lstrip('_')
        if isinstance(block,BasicBlock):
            return self.s+res
        return res
    def getenergy_(self,block):
        '''Get energy from JSON file'''
        if isinstance(block,Function):
            return 0
        if self.mapping:
            fnmap=[f for f in self.mapping['program']['functions'] if f['name']==block.function.name][0]
            tmp=[b for b in fnmap['blocks']
                 if b['name']==block.function.name+'_'+block.name][0]
            phitmp=len([i for i in block.instructions if i.opcode_name=='phi'])*150000 #IGNORE 
            return int(tmp['energy'])-phitmp
        assert False, "no json file specified"
        
    def getenergy(self,block):
        if isinstance(block,Function):
            return 0
        armdef=13
        res=0
        prev=None
        for i in block.instructions:
            op=i.opcode_name
            prev=op
            if op =='add' and prev=='mul':
                # multiply accumulate, energy has been accounted for
                continue
            if op in ['udiv','urem','sdiv','srem']:
                res+=armdef*5
                continue
            if op=='call' and i.called_function and i.called_function.name.startswith('llvm.dbg'):
                continue
            if op=='call':
                res+=armdef*(1+len(i.operands))
                continue
            if op=='phi':
                res+=armdef*0.5
                continue
            if op=='getelementptr':
                res+=armdef*(len(i.operands)-1)
                continue
            if op=='ret':
                res+=armdef*3
            if op=='br':
                res+=armdef*(len(i.operands)-1)
                continue
            if op in ['load','store']:
                res+=armdef*2
                continue
            res+=armdef
        return int(res)
            


class PubsSolver(Solver):
    def genexp(self,arg):
        '''Generates PUBS expression from internal expression format. Inductively applied to the structure of an expression and spits out the result.'''
        op,r0,*rst=arg
        if rst:
            r1=rst[0]
        ge=self.genexp
        if op in {'var','phi','arg'}: return self.vartostr(r0)
        if op=='const':
            return str(r0)
        if op=='!':
            # transform the expression
            op,*rst=r0
            if iscondition(op):
                transformed=inverse_op[op],rst[0],rst[1]
                return ge(transformed)
            return '?'
        if op=='&&':
            return ge(r0)+','+ge(rst[0])
        if op=='||':
            return ge(r0)
        if op=='?':
            return '?'
        if op in {'>=','-','+','*','/','<='}:
            if (r0[0],r1[0])==('const','const'):
                # evaluate constants
                res=str(int(eval('%s %s %s'%(r0[1],op,r1[1]))))
                return res
            #HACK
            if op=='<=': op='='
            return '%s %s %s'%(ge(r0),op,ge(r1))
        if op=='<':
            return ge(('<=',r0,('-',r1,('const','1'))))
        if op=='>':
            return ge(('>=',r0,('+',r1,('const','1'))))
        if op=='==':
            return ge(r0)+'='+ge(r1)
        if op=='!=':
            #TODO wrong
            return ge(('>',r0,r1))
        if op=='range':
            return '?'
        assert False, arg


    replacements={'>':'g','=':'eq','*':'m','/':'d','<':'l','.':''}
    def vartostr(self,var):
        if isinstance(var,str):
            return var
        if isinstance(var,Argument):
            return 'In'+str(var).split('%')[-1]
        assert isinstance(var,Instruction),var
        name='V'+var.name
        for k,v in self.replacements.items():
            name=name.replace(k,v)
        return name
    def gencond(self,c):
        exp=self.genexp(c)
        # Uncomment the following code if you want to avoid manually tweaking the
        # generated side conditions.
        #if '?' in exp:
        #    return ''
        if not any(op in exp for op in inverse_op):
            return ''
        return exp
    
    def __init__(self):
        self.lines=[]

    def transformdivision(self,continuations,conditions):
        n=0
        for cont,formals_after in continuations:
            for i,f in enumerate(formals_after):
                if f[0]=='/':
                    rep=('var','DIV%d'%n)
                    n+=1
                    formals_after[i]=rep
                    def replace(cond):
                        if cond==f:
                            return rep
                        if not isinstance(cond,tuple):
                            # primitive value
                            return cond
                        # recursive case
                        op,*args=cond
                        return tuple([op]+[replace(a) for a in args])
                    for j,cond in enumerate(conditions):
                        conditions[j]=replace(cond)
                    conditions.append(('>=',f[1],('*',rep,f[2])))
                
    def addrel(self,block,formals,continuations,conditions):
        self.transformdivision(continuations,conditions)
        blockname=self.codetostr(block)
        rhs=[]
        for cont,formals_after in continuations:
            contname=self.codetostr(cont)
            formals_after=','.join(self.genexp(f) for f in list(formals_after))
            if formals_after:
                formals_after='('+formals_after+')'
            rhs.append(contname+formals_after)
        formals=','.join(self.vartostr(f._) for f in formals)
        if formals:
            formals='('+formals+')'
        components=','.join(rhs)
        conditions=','.join(self.gencond(c) for c in conditions)
        energy=self.getenergy(block)
        self.lines.append('eq({blockname}{formals},{energy},[{components}],[{conditions}]).'.format(**locals()))

    def solve(self,entry=None,**args):
        print('\n'.join(self.lines))

blockenergy=1
class NumericSolver(Solver):
    def __init__(self):
        self.eqns=defaultdict(list)
    def addrel(self,block,formals,continuations,conditions):
        self.eqns[self.codetostr(block)].append(
            (block,formals,continuations,conditions))

    def trigger(self,conditions,envd):
        # create env dictionary
        return all(self.eval_arg(envd,c) for c in conditions)

    def eval_arg(self,envd,arg):
        opcode,*operands=arg
        if operands:
            o0=operands[0]
        ea=lambda a:self.eval_arg(envd,a)
        if opcode in ['arg','var','phi']:
            return envd.get(LLVMElem(o0),'?')
        if opcode=='!': return not ea(o0)
        if opcode in binops:
            # binop
            return eval(repr(ea(o0))+opcode+repr(ea(operands[1])))
        if opcode == 'const':
            return int(o0)
        if opcode=='?':
            return '?'
        import pdb; pdb.set_trace()

    def calcenv(self,env,formals_after):
        return [self.eval_arg(env,arg) for arg in formals_after]
        
            
    def solve(self,entry,env):
        '''Implements a CR interpreter'''
        maxenergy=0
        for (block,formals,continuations,conditions) in self.eqns[entry]:
            # check side conditions
            envd=dict(zip(formals,env))
            if not self.trigger(conditions,envd):
                continue
            energy=self.getenergy(block)
            for cont,formals_after in continuations:
                contname=self.codetostr(cont)
                newenv=self.calcenv(envd,formals_after)
                energy+=self.solve(contname,newenv)
            if energy>maxenergy:
                maxenergy=energy
        return maxenergy
            
class LLVMElem:
    def __init__(self,_):
        self._=_
        assert not isinstance(_,ConstantInt)
    def __eq__(self,other):
        return isinstance(other,LLVMElem) and other._ == self._
    def __hash__(self):
        return hash(self._.name) + 233
    def __str__(self):
        return str(self._.name)
    __repr__=__str__

def iscondition(op):
    return op in inverse_op

def tosigned(i):
    '''This function is a dirty hack'''
    if i>=0x7FFFFFFFFFFFFFFF:
        i= -((i ^ 0xFFFFFFFFFFFFFFFF)+1)
    if i>=0x7FFFFFFF:
        i= -((i ^ 0xFFFFFFFF)+1)
    if i>=0x7FFF:
        i= -((i ^ 0xFFFF)+1)
    return i

def inter(branches):
    if not branches:
        return []
    elif len(branches)==1:
        return branches[0]
    elif len(branches)==2:
        return set(branches[0]) & set(branches[1])
    else:
        assert False
        
class Inferencer:
    call_exclude={'llvm.dbg.declare','llvm.dbg.value','llvm.trap'}
    def __init__(self,solver,fn,s):
        self.s=s
        self.solver=solver
        self.fn=fn
        self.trail=set()
        if self.fn.basic_block_count:
            self.assignblocknames()
            self.getcontgraph()
            self.getvars()
            #self.print_in_out()
            self.infer()

    def getarg(self,block,var):
        assert isinstance(block,BasicBlock),block
        ga=lambda var: self.getarg(block,var)
        if isinstance(var,Argument):
            return 'arg',var
        if isinstance(var,ConstantInt):
            return 'const',str(tosigned(var.z_ext_value))
        if isinstance(var,ConstantFP):
            return '?',None
        if isinstance(var,ConstantExpr):
            return '?',None
        if isinstance(var,ConstantPointerNull):
            return '?',None
        if isinstance(var,UndefValue):
            return 'const',0
        assert isinstance(var,Instruction),str(var)
        if var.opcode_name=='phi':
            return 'phi',var
        if var.opcode_name=='load':
            return '?',None
        if var.opcode_name=='getelementptr':
            return '?',None
        if var.basic_block!=block:
            return 'var',var
        if var.opcode_name=='sub':
            return '-',ga(var.operands[0]),ga(var.operands[1])
        if var.opcode_name=='add':
            return '+',ga(var.operands[0]),ga(var.operands[1])
        if var.opcode_name in ('mul','fmul'):
            return '*',ga(var.operands[0]),ga(var.operands[1])
        if var.opcode_name=='shl':
            op0=ga(var.operands[0])
            op1=ga(var.operands[1])
            if op1[0]=='const':
                return '*',op0,('const',int(pow(2,float(op1[1]))))
            return '?',None
        if var.opcode_name in ('shr','ashr','lshr'):
            op0=ga(var.operands[0])
            op1=ga(var.operands[1])
            if op1[0]=='const':
                return '/',op0,('const',int(pow(2,float(op1[1]))))
            return '?',None
        if var.opcode_name in ('udiv','fdiv'):
            return '/',ga(var.operands[0]),ga(var.operands[1])
        if var.opcode_name in ('srem','urem'):
            # upper bound of modulus is actually an approximation
            #return '-',ga(var.operands[1]),('const','1')
            return '/',ga(var.operands[1]),('const','2')
        if var.opcode_name in ('zext','sitofp'):
            return ga(var.operands[0])
        if var.opcode_name=='alloca':
            return 'const','0'
        if var.opcode_name=='and':
            op0=ga(var.operands[0])
            op1=ga(var.operands[1])
            if op1[0]=='const':
                return 'range',op1,('const','0')
            return '&&',op0,op1
        if var.opcode_name=='or':
            return '||',ga(var.operands[0]),ga(var.operands[1])
        if var.opcode_name=='icmp':
            if ' sle ' in str(var):
                return '<=', ga(var.operands[0]), ga(var.operands[1])
            if ' uge ' in str(var) or ' sge ' in str(var):
                return '>=', ga(var.operands[0]), ga(var.operands[1])
            if ' ne ' in str(var):
                op0=ga(var.operands[0])
                op1=ga(var.operands[1])
                if op1==('const','0') and iscondition(op0[0]):
                    return op0
                return '!=',op0,op1
            if ' eq ' in str(var):
                return '==',ga(var.operands[0]),ga(var.operands[1])
            if ' slt ' in str(var) or ' ult ' in str(var):
                return '<', ga(var.operands[0]), ga(var.operands[1])
            if ' sgt ' in str(var) or ' ugt 'in str(var):
                return '>', ga(var.operands[0]), ga(var.operands[1])
        if var.opcode_name=='trunc':
            return ga(var.operands[0])
        if var.opcode_name=='sext':
            return ga(var.operands[0])
        if var.opcode_name=='call':
            return '?',None
        if var.opcode_name=='select':
            #TODO select
            return '?',None
        if var.opcode_name=='extractvalue':
            return '?',None
        if var.opcode_name=='bitcast':
            return '?',None
        if var.opcode_name=='xor':
            return '?',None
        assert False,str(var)



    def printeqn(self,block,formals,continuations=[],conditions=[]):
        self.solver.s=self.s
        self.solver.addrel(block,formals,continuations,conditions)

    def genargs(self,block):
        branch=block._.instructions[-1]
        res=set()
        if branch.opcode_name=='br' and len(branch.operands)>1:
            self.get_vars_from_arg(res,self.getarg(block._,branch.operands[0]))
        # get called functions
        for inst in block._.instructions:
            if self.iscall(inst):
                for i in inst.operands[:-1]:
                    self.get_vars_from_arg(res,self.getarg(block._,i))
        if self.fn.entry_basic_block==block._:
            for i,arg in enumerate(self.fn.args):
                res.add(LLVMElem(arg))
        for r in res:
            assert not isinstance(r._,ConstantInt)
        return res

    def killargs(self,block):
        res=set()
        for inst in block._.instructions:
            if inst.opcode_name!='phi':
                res.add(LLVMElem(inst))
        return res

    def get_vars_from_arg(self,out,arg):
        op,*rst=arg
        if op in {'phi','var','arg'}:
            # make sure a non boolean integer
            if isinstance(rst[0].type,IntegerType) and rst[0].type.width>1:
                out.add(LLVMElem(rst[0]))
        elif op in {'?','const'}:
            pass
        else:
            for r in rst:
                self.get_vars_from_arg(out,r)

    def getsuccessors(self,block):
        branch=block._.instructions[-1]
        if branch.opcode_name!='br':
            return []
        if len(branch.operands)==1:
            return [LLVMElem(branch.operands[0])]
        return [LLVMElem(branch.operands[1]),LLVMElem(branch.operands[2])]

    def getvars(self):
        '''Fixpoint algorithm for inferring input arguments'''
        self.vars=dict((LLVMElem(bb),set()) for bb in self.fn.basic_blocks)
        oldvars=None
        # fixpoint algorithm
        while self.vars!=oldvars:
            # make a copy of current structure
            oldvars=dict((k,set(v)) for k,v in self.vars.items())
            # transfer through cfg
            for k in oldvars.keys():
                # get input args of successors
                for succ in self.getsuccessors(k):
                    for var in set(self.vars[succ]):
                        if getattr(var._,'opcode_name',None)=='phi' and LLVMElem(var._.basic_block)==succ:
                            for n in range(var._.operand_count):
                                inblock=LLVMElem(var._.get_incoming_block(n))
                                if inblock!=k:
                                    continue
                                val=var._.get_incoming_value(n)
                                if not isinstance(val, (Argument, Instruction)):
                                    continue
                                #self.vars[k].add(LLVMElem(val))
                                self.get_vars_from_arg(self.vars[k],self.getarg(k._,val))
                        else:
                            self.get_vars_from_arg(self.vars[k],self.getarg(k._,var._))
                            #self.vars[k].add(var)
                # add/remove original vars
                self.vars[k]-=self.killargs(k)
                self.vars[k]|=self.genargs(k)

    def iscall(self,inst):
        return (inst.opcode_name=='call' and inst.called_function and
                inst.called_function.name not in self.call_exclude)

    def callsitself(self,begin,end):
        if begin in self.trail:
            return True
        try:
            self.trail.add(begin)
            if begin==end:
                return True
            dsts=self.contgraph[begin]
            return bool(dsts) and all(
                all(self.callsitself(b,end) for b in bs)
                       for bs in dsts)
        finally:
            self.trail.remove(begin)

    def outputcontgraph(self,fn):
        with open(fn,'w') as f:
            for k,vss in self.contgraph.items():
                f.write('digraph %s {\n'%k.replace('.',''))
                for vs in vss:
                    if not vs:
                        vs=['_']
                    f.write('->'.join(a.replace('.','') for a in [k]+vs)+';\n')
                f.write('}\n')

    def assignblocknames(self):
        i=0
        j=0
        for bb in self.fn.basic_blocks:
            if not bb.name:
                bb.name='bb'+str(i)
                i+=1
            for inst in bb.instructions:
                if not inst.name and not inst.type._ptr.isVoidTy():
                    inst.name='ii'+str(j)
                    j+=1
                    

    def getcontgraph(self):
        ''' construct and transform continuation graph'''
        # Construct initial 'continuation graph'
        contgraph={}
        self.contgraph=contgraph
        for bb in self.fn.basic_blocks:
            branch=bb.instructions[-1]
            if branch.opcode_name!='br':
                branches=[]
            else:
                if len(branch.operands)==1:
                    branches=[[branch.operands[0].name]]
                else:
                    branches=[[branch.operands[1].name],[branch.operands[2].name]]
            contgraph[bb.name]=branches
        #self.outputcontgraph('before.dot')
        # done, now let's find the loops. Note that the following algorithm
        # can be replaced with your favourite one if it doesn't work.
        loops=set()
        for tr,fa in [(0,1),(1,0)]:
            # assume # of edges is 2 
            # try all combinations of consequent/alt edge
            for k,vs in contgraph.items():
                if not vs or len(vs)==1:
                    continue
                assert len(vs)==2
                # step one, find loop re-entries
                if (not self.callsitself(vs[tr][0],k) and
                    self.callsitself(vs[fa][0],k)):
                    # find loop headers
                    head=vs[fa][0]
                    # find reentry
                    reentry=k
                    # find exit
                    exit=vs[tr][0]
                    # find entry
                    entries=[kk for kk,vv in contgraph.items()
                              if any((head in v) for v in vv)
                                 and kk!=reentry]
                    if len(entries)==0:
                        continue
                    assert len(entries)==1
                    entry=entries[0]
                    # store header, re-entry, entry, exit triple
                    loops.add((head,reentry,entry,exit))
        #print(loops)
        # found the loops, now let's perform the transformations
        for head,reentry,entry,exit in loops:
            # remove ref from reentry to exit
            if contgraph[reentry][0]==[exit]:
                contgraph[reentry][0]=[]
            if contgraph[reentry][1]==[exit]:
                contgraph[reentry][1]=[]
            # add ref from entry to exit
            for vs in contgraph[entry]:
                if exit not in vs:
                    vs.append(exit)
        #self.outputcontgraph('after.dot')
        # We construct a dictionary mapping block names to blocks
        blockdict=dict((bb.name,bb) for bb in self.fn.basic_blocks)
        # we now replace block names in the values with the actual blocks
        for k,vs in contgraph.items():
            for i,v in enumerate(vs):
                vs[i]=[blockdict[block] for block in v]
        self.contgraph=contgraph
    
    def infer(self):
        '''Traverse all blocks and produces CRs which are passed onto solver instance. '''
        entry=self.fn.entry_basic_block
        self.printeqn(self.fn,[LLVMElem(a) for a in self.fn.args],[(entry,[('arg',arg) for arg in self.fn.args])])
        # get branches
        for bb in self.fn.basic_blocks:
            continuations=[]
            branch=bb.instructions[-1]
            inputvars=self.vars[LLVMElem(bb)]
            # check if there is a call
            for inst in bb.instructions:
                if self.iscall(inst):
                    params=[self.getarg(bb,op) for op in inst.operands[:-1]]
                    continuations.append((inst.called_function,params))
            if branch.opcode_name=='br':
                def getcontinuations(bb,i):
                    nextblocks=self.contgraph[bb.name][i]
                    return continuations+[(n,self.peval_vars(bb,n))
                                          for n in nextblocks]
                if len(branch.operands)==1:
                    self.printeqn(bb,inputvars,getcontinuations(bb,0))
                    #continuations+[(next_block,self.peval_vars(bb,next_block))]
                else:
                    pred=branch.operands[0]
                    cond=self.getarg(bb,pred)
                    # branch on predicate false is at position 0
                    self.printeqn(bb,inputvars,getcontinuations(bb,0),[('!',cond)])
                    # branch on predicate true is at position 1
                    self.printeqn(bb,inputvars,getcontinuations(bb,1),[cond])
            else:
                self.printeqn(bb,inputvars,continuations)

    def transfer_vars(self,bbOut,bbIn):
        vars_in=self.vars[LLVMElem(bbIn)]
    def print_in_out(self):
        '''Function that helps debug the data flow analysis'''
        for block in self.fn.basic_blocks:
            print('%======='+block.name)
            for var in self.vars[LLVMElem(block)]:
                print('%',var._)

    def peval_vars(self,bb,next_block):
        '''Partially evaluate the variables we are interested in with respect to a block.'''
        vars=[]
        for var_ in self.vars[LLVMElem(next_block)]:
            var=var_._
            if (getattr(var,'opcode_name',None)=='phi' and
                var.basic_block==next_block):
                for n in range(var.operand_count):
                    inblock=var.get_incoming_block(n)
                    if inblock==bb:
                        var=var.get_incoming_value(n)
                        break
            var=self.getarg(bb,var)
            vars.append(var)
        return vars

def main(_,bitcodefile,jsonfile=None):
    with open(bitcodefile,'rb') as f:
        mod_bc=Module.from_bitcode(f)
#    solver=NumericSolver()
    solver=PubsSolver()
    if jsonfile is not None:
        with open(jsonfile) as f:
            solver.mapping=json.load(f)
    for i,fn in enumerate(mod_bc.functions):
        infer=Inferencer(solver,fn,'f%d'%i)
#        fn.viewCFG()
    solver.solve()
#    res=solver.solve(mod_bc.functions[0].name,['?',4,6])
#    print(res)
#        infer.print_in_out()

def excepthook(type,value,tb):
    import traceback, pdb
    # we are NOT in interactive mode, print the exception...
    traceback.print_exception(type, value, tb)
    print
    # ...then start the debugger in post-mortem mode.
    pdb.pm()

sys.excepthook=excepthook

if __name__=='__main__':
    main(*sys.argv)
