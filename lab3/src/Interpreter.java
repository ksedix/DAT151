import cmm.Absyn.*;
import cmm.Yylex;
import cmm.parser;

import java.io.FileReader;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Scanner;


public class Interpreter {

    Scanner scanner = new Scanner(System.in);

    public void interpret(Program p) {
        //throw new RuntimeException("Not yet an interpreter");
        Env env = new Env();
        PDefs pDefs = (PDefs) p;
        //Add all function definitions to the environment. This includes the function argument list and function body
        for (Def def : pDefs.listdef_){
            DFun dFun = (DFun) def;
            env.updateFun(dFun.id_,dFun);
        }

        //evaluate the main function. The expression that calls the main function.
        DFun main = env.lookupFun("main");
        for (Stm stm : main.liststm_){
            Object value = stm.accept(new StmValue(),env);
            if (value instanceof Val){
                break;
            }
        }
    }



    public static class Env{

        //for each variable in each context, store its value
        public LinkedList<HashMap<String,Val>> contexts = new LinkedList<>();
        //Store function definition(function signature + function body)
        public HashMap<String,DFun> definitions = new HashMap<>();

        public Val lookupVar(String id){
            for (HashMap<String,Val> context : contexts){
                if (context.containsKey(id)){
                    if (context.get(id) == null){
                        throw new RuntimeException("Variable has not been initialized");
                    } else {
                        return context.get(id);
                    }
                }
            }
            //this will not happen, because type-checking will find first if the variable has not been declared.
            throw new RuntimeException("Variable has not been declared");
        }

        public DFun lookupFun(String id){
            if (definitions.containsKey(id)) {
                return definitions.get(id);
            }
            throw new RuntimeException("Function with id " + id + " has not been defined");
        }

        //this function is necessary for initializing a new variable
        public void updateVar(String id, Val value){
            if (contexts.isEmpty()){
                newBlock();
            }
            contexts.get(0).put(id,value);
        }

        public int contextNr(String id){
            for (int i=0;i<contexts.size();i++){
                HashMap<String,Val> context = contexts.get(i);
                if (context.containsKey(id)){
                    return i;
                }
            }
            return 0;
        }

        public void declareVar(String id){
            if (contexts.isEmpty()){
                newBlock();
            }
            contexts.get(0).put(id,null);
        }


        public void updateFun(String id, DFun funDef){
            if (!definitions.containsKey(id)){
                definitions.put(id,funDef);
            } else {
                throw new RuntimeException("Function with id "+id+" has already been defined");
            }
        }



        //this function is necessary for updating the value of an existing variable
        public void updateVarInContext(String id, int contextNr, Val value){
            Val oldVal = contexts.get(contextNr).get(id);
            if (oldVal instanceof VDouble) {
                contexts.get(contextNr).put(id, castToDouble(value));
            } else {
                contexts.get(contextNr).put(id,value);
            }
        }

        public void newBlock(){
            this.contexts.addFirst(new HashMap<String,Val>());
        }

        public void exitBlock(){
            this.contexts.pop();
        }

    }

    private class StmValue implements Stm.Visitor<Object,Env> {

        @Override
        public Object visit(SExp p, Env arg) {
            //The expression is evaluated, but its value is ignored
            p.exp_.accept(new ExpValue(),arg);
            //the modified environment is returned.
            return arg;
        }

        @Override
        public Object visit(SDecls p, Env arg) {
            for (String id : p.listid_){
                //declare the var, but do not initialize it with a value.
                arg.declareVar(id);
            }
            return arg;
        }

        @Override
        public Object visit(SInit p, Env arg) {
            //first declare the var so that it exists in the environment. This is necessary so that expressions such as
            //int x = x+5 will be invalidated.
            arg.declareVar(p.id_);
            if (p.type_ instanceof Type_double) {
                //an expression like int x = x+1 will not be accepted because it will look for the value of x which will be null.
                arg.updateVar(p.id_, castToDouble(p.exp_.accept(new ExpValue(), arg)));
            } else {
                arg.updateVar(p.id_,p.exp_.accept(new ExpValue(),arg));
            }
            return arg;
        }

        @Override
        public Object visit(SReturn p, Env arg) {
            return p.exp_.accept(new ExpValue(),arg);
        }

        @Override
        public Object visit(SWhile p, Env arg) {
            VBool vBool = (VBool) p.exp_.accept(new ExpValue(),arg);
            if (vBool.equals(False)){
                return arg;
            } else {
                arg.newBlock();
                Object rv = p.stm_.accept(this,arg);
                if (rv instanceof Val){
                    arg.exitBlock();
                    return rv;
                }
                arg.exitBlock();
                p.accept(this,arg);
            }
/*            while (true) {
                if (p.exp_.accept(new ExpValue(), arg).equals(True)) {
                    arg.newBlock();
                    p.stm_.accept(this, arg);
                    arg.exitBlock();
                } else {
                    break;
                }
            }*/
            return arg;
        }

        @Override
        public Object visit(SBlock p, Env arg) {
            arg.newBlock();
            for (Stm stm : p.liststm_){
                Object rv = stm.accept(this,arg);
                if (rv instanceof Val){
                    arg.exitBlock();
                    return rv;
                }
            }
            arg.exitBlock();
            return arg;
        }

        @Override
        public Object visit(SIfElse p, Env arg) {
            if (p.exp_.accept(new ExpValue(),arg).equals(True)){
                arg.newBlock();
                Object rv = p.stm_1.accept(this,arg);
                if (rv instanceof Val){
                    arg.exitBlock();
                    return rv;
                }
                arg.exitBlock();
            } else {
                arg.newBlock();
                Object rv = p.stm_2.accept(this,arg);
                if (rv instanceof Val){
                    arg.exitBlock();
                    return rv;
                }
                arg.exitBlock();
            }
            return arg;
        }

    }

    public Val addVal(Val val1, Val val2, AddOp op){
        if (val1 instanceof VDouble || val2 instanceof VDouble){
            VDouble vDouble1 = castToDouble(val1);
            VDouble vDouble2 = castToDouble(val2);
            if (op instanceof OPlus){
                return new VDouble(vDouble1.double_ + vDouble2.double_);
            } else {
                return new VDouble(vDouble1.double_ - vDouble2.double_);
            }
        } else {
            VInteger vInteger1 = (VInteger) val1;
            VInteger vInteger2 = (VInteger) val2;
            if (op instanceof OPlus){
                return new VInteger(vInteger1.integer_ + vInteger2.integer_);
            } else {
                return new VInteger(vInteger1.integer_ - vInteger2.integer_);
            }
        }
    }

    public Val mulVal(Val val1, Val val2, MulOp op){
        if (val1 instanceof VDouble || val2 instanceof VDouble){
            VDouble vDouble1 = castToDouble(val1);
            VDouble vDouble2 = castToDouble(val2);
            if (op instanceof OTimes){
                return new VDouble(vDouble1.double_*vDouble2.double_);
            } else {
                return new VDouble(vDouble1.double_/vDouble2.double_);
            }
        } else {
            VInteger vInteger1 = (VInteger) val1;
            VInteger vInteger2 = (VInteger) val2;
            if (op instanceof OTimes){
                return new VInteger(vInteger1.integer_*vInteger2.integer_);
            } else {
                return new VInteger(vInteger1.integer_/vInteger2.integer_);
            }
        }
    }

    public static VDouble castToDouble(Val value){
        if (value instanceof VInteger){
            Double n = Double.valueOf(((VInteger) value).integer_);
            return new VDouble(n);
        } else {
            VDouble vDouble = (VDouble) value;
            return vDouble;
        }
    }

    public VBool cmpVal(Val val1, Val val2, CmpOp cmpOp){

        if (cmpOp instanceof OEq){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (vDouble1.equals(vDouble2)){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (vInteger1.equals(vInteger2)){
                    return True;
                } else {
                    return False;
                }
            } else {
                VBool vBool1 = (VBool) val1;
                VBool vBool2 = (VBool) val2;
                if (vBool1.equals(vBool2)){
                    return True;
                } else {
                    return False;
                }
            }
        } else if (cmpOp instanceof ONEq){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (!vDouble1.equals(vDouble2)){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (!vInteger1.equals(vInteger2)){
                    return True;
                } else {
                    return False;
                }
            } else {
                VBool vBool1 = (VBool) val1;
                VBool vBool2 = (VBool) val2;
                if (!vBool1.equals(vBool2)){
                    return True;
                } else {
                    return False;
                }
            }

        } else if (cmpOp instanceof OGt){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (vDouble1.double_.compareTo(vDouble2.double_)>0){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (vInteger1.integer_.compareTo(vInteger2.integer_)>0){
                    return True;
                } else {
                    return False;
                }}
        } else if (cmpOp instanceof OLt){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (vDouble1.double_.compareTo(vDouble2.double_)<0){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (vInteger1.integer_.compareTo(vInteger2.integer_)<0){
                    return True;
                } else {
                    return False;
                }}

        } else if (cmpOp instanceof OLtEq){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (vDouble1.double_.compareTo(vDouble2.double_)<0 || vDouble1.double_.compareTo(vDouble2.double_)==0){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (vInteger1.integer_.compareTo(vInteger2.integer_)<0 || vInteger1.integer_.compareTo(vInteger2.integer_)==0){
                    return True;
                } else {
                    return False;
                }}
        } else if (cmpOp instanceof OGtEq){
            if (val1 instanceof VDouble || val2 instanceof VDouble){
                VDouble vDouble1 = castToDouble(val1);
                VDouble vDouble2 = castToDouble(val2);
                if (vDouble1.double_.compareTo(vDouble2.double_)>0 || vDouble1.double_.compareTo(vDouble2.double_)==0){
                    return True;
                } else {
                    return False;
                }
            } else if (val1 instanceof VInteger){
                VInteger vInteger1 = (VInteger) val1;
                VInteger vInteger2 = (VInteger) val2;
                if (vInteger1.integer_.compareTo(vInteger2.integer_)>0 || vInteger1.integer_.compareTo(vInteger2.integer_)==0){
                    return True;
                } else {
                    return False;
                }}
        }
        return null;
    }

    //when we update a variable, using an expression, we must update the variable in the correct context.
    public void postVal(EPost p, Env arg){
        Val value = arg.lookupVar(p.id_);
        int contextNr = arg.contextNr(p.id_);
        if (p.incdecop_ instanceof OInc) {
            if (value instanceof VInteger) {
                arg.updateVarInContext(p.id_,contextNr, new VInteger(((VInteger) value).integer_ + 1));
            } else if (value instanceof VDouble) {
                arg.updateVarInContext(p.id_,contextNr, new VDouble(((VDouble) value).double_ + 1));
            }
        } else {
            if (value instanceof VInteger) {
                arg.updateVarInContext(p.id_,contextNr, new VInteger(((VInteger) value).integer_ - 1));
            } else if (value instanceof VDouble) {
                arg.updateVarInContext(p.id_,contextNr, new VDouble(((VDouble) value).double_ - 1));
            }
        }
    }

    public void preVal(EPre p, Env arg){
        Val value = arg.lookupVar(p.id_);
        int contextNr = arg.contextNr(p.id_);
        if (p.incdecop_ instanceof OInc) {
            if (value instanceof VInteger) {
                arg.updateVarInContext(p.id_,contextNr, new VInteger(((VInteger) value).integer_ + 1));
            } else if (value instanceof VDouble) {
                arg.updateVarInContext(p.id_,contextNr, new VDouble(((VDouble) value).double_ + 1));
            }
        } else {
            if (value instanceof VInteger) {
                arg.updateVarInContext(p.id_,contextNr, new VInteger(((VInteger) value).integer_ - 1));
            } else if (value instanceof VDouble) {
                arg.updateVarInContext(p.id_,contextNr, new VDouble(((VDouble) value).double_ - 1));
            }
        }
    }

    public static VBool True = new VBool(1);
    public static VBool False = new VBool(0);

    private class ExpValue implements Exp.Visitor<Val, Env> {

        @Override
        public Val visit(EBool p, Env arg) {
            if (p.boollit_ instanceof LTrue){
                return True;
            } else {
                return False;
            }
        }

        @Override
        public Val visit(EInt p, Env arg) {
            return new VInteger(p.integer_);
        }

        @Override
        public Val visit(EDouble p, Env arg) {
            return new VDouble(p.double_);
        }

        @Override
        public Val visit(EId p, Env arg) {
            return arg.lookupVar(p.id_);
        }

        @Override
        public Val visit(EApp p, Env arg) {
            Val rv = null;
            if (p.id_.equals("printInt")){
                VInteger vInteger = (VInteger) p.listexp_.get(0).accept(this,arg);
                System.out.printf("%d\n", vInteger.integer_);
            } else if (p.id_.equals("printDouble")){
                Val value = p.listexp_.get(0).accept(this,arg);
                if (value instanceof VInteger) {
                    VDouble dVal = castToDouble(value);
                    System.out.println(dVal.double_);
                } else {
                    VDouble dVal = (VDouble) value;
                    System.out.println(dVal.double_);
                }
            } else if (p.id_.equals("readInt")){
                int result = scanner.nextInt();
                return new VInteger(result);
            } else if (p.id_.equals("readDouble")){
                double result = scanner.nextDouble();
                return new VDouble(result);
            } else {
                DFun funDef = arg.lookupFun(p.id_);
                LinkedList<Val> values = new LinkedList<>();
                for (int i = 0; i < p.listexp_.size(); i++) {
                    Val value = p.listexp_.get(i).accept(this, arg);
                    values.add(value);
                }
                arg.newBlock();
                for (int i = 0; i < funDef.listarg_.size();i++){
                    ADecl aDecl = (ADecl) funDef.listarg_.get(i);
                    //cast the arguments to the function to type double if the function parameters are double and the arguments are of type int.
                    if (aDecl.type_ instanceof Type_double && values.get(i) instanceof VInteger) {
                        arg.updateVar(aDecl.id_, castToDouble(values.get(i)));
                    } else {
                        arg.updateVar(aDecl.id_, values.get(i));
                    }
                }
                for (Stm stm : funDef.liststm_) {
                    //the statement visitor returns either an environment or a Val(in case there is a return statement)
                    //the val can be either a value from an expression, such as a double, bool or int. SReturn return 4;
                    //what happens if there is a return statement within a while loop? It will return. but will it exit the while loop?
                    Object val = stm.accept(new StmValue(),arg);
                    //check if the value returned is an instance of Val, in this case there was a return statement somewhere
                    if (val instanceof Val){
                        arg.exitBlock();
                        if (funDef.type_ instanceof Type_double && val instanceof VInteger) {
                            return castToDouble((Val) val);
                        } else {
                            return (Val) val;
                        }
                    }
                    /*if (stm instanceof SReturn) {
                        rv = ((SReturn) stm).exp_.accept(new ExpValue(), arg);
                        break;
                    } else {
                        stm.accept(new StmValue(), arg);
                    }*/
                }
                arg.exitBlock();
            }
            return rv;
        }

        @Override
        public Val visit(EPost p, Env arg) {
            Val value = arg.lookupVar(p.id_);
            postVal(p,arg);
            return value;
        }

        @Override
        public Val visit(EPre p, Env arg) {
            preVal(p,arg);
            return arg.lookupVar(p.id_);
        }

        @Override
        public Val visit(EMul p, Env arg) {
            Val val1 = p.exp_1.accept(this,arg);
            Val val2 = p.exp_2.accept(this,arg);
            return mulVal(val1,val2,p.mulop_);
        }

        @Override
        public Val visit(EAdd p, Env arg) {
            Val val1 = p.exp_1.accept(this,arg);
            Val val2 = p.exp_2.accept(this,arg);
            return addVal(val1,val2,p.addop_);
        }

        @Override
        public Val visit(ECmp p, Env arg) {
            Val val1 = p.exp_1.accept(this,arg);
            Val val2 = p.exp_2.accept(this,arg);
            return cmpVal(val1,val2,p.cmpop_);
        }

        @Override
        public Val visit(EAnd p, Env arg) {
            if (p.exp_1.accept(this,arg).equals(True)){
                //type checking guarantees that both operands are of type bool.
                return p.exp_2.accept(this,arg);
            } else {
                return False;
            }
        }

        @Override
        public Val visit(EOr p, Env arg) {
            if (p.exp_1.accept(this,arg).equals(True)){
                return True;
            } else {
                return p.exp_2.accept(this,arg);
            }
        }

        @Override
        public Val visit(EAss p, Env arg) {
            //assign the value of the variable to the innermost occurrence of the id. This could be the current scope or a parent scope.
            Val value = p.exp_.accept(this,arg);
            int contextNr = arg.contextNr(p.id_);
            arg.updateVarInContext(p.id_,contextNr,value);
            return value;
        }

        @Override
        public Val visit(ETyped p, Env arg) {
            return p.exp_.accept(this,arg);
        }

    }

}