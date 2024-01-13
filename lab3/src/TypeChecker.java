import cmm.Absyn.*;
import cmm.VisitSkel;

import java.util.HashMap;
import java.util.LinkedList;

public class TypeChecker {

  public static enum TypeCode {CInt, CDouble, CBool, CVoid}

  //correct
  public static TypeCode typeCode (Type ty){
    return ty.accept(new TypeCodeVisitor(),null);
  }

  public static class TypeCodeVisitor implements Type.Visitor<TypeCode,Type>{
    @Override
    public TypeCode visit(Type_bool p, Type arg) {
      return TypeCode.CBool;
    }

    @Override
    public TypeCode visit(Type_int p, Type arg) {
      return TypeCode.CInt;
    }

    @Override
    public TypeCode visit(Type_double p, Type arg) {
      return TypeCode.CDouble;
    }

    @Override
    public TypeCode visit(Type_void p, Type arg) {
      return TypeCode.CVoid;
    }
  }


  public static class FunType {
    public ListArg args;
    public Type type;

    public FunType(Type val, ListArg args){
      this.type = val;
      this.args = args;
    }

  }

  public static class Env {

    public Env(){
      ListArg printIntArgs = new ListArg();
      ListArg printDoubleArgs = new ListArg();
      printIntArgs.add(new ADecl(new Type_int(),"i"));
      printDoubleArgs.add(new ADecl(new Type_double(),"d"));
      this.updateFun("printInt",new FunType(new Type_void(),printIntArgs));
      this.updateFun("printDouble",new FunType(new Type_void(),printDoubleArgs));
      this.updateFun("readInt",new FunType(new Type_int(),new ListArg()));
      this.updateFun("readDouble",new FunType(new Type_double(),new ListArg()));
    }

    public Type funType;

    public HashMap<String, FunType> signatures = new HashMap<>();
    public LinkedList<HashMap<String, Type>> contexts = new LinkedList<>();

    public Type lookupVar(String id) {
      for (HashMap<String, Type> context : contexts) {
        if (context.containsKey(id)) {
          return context.get(id); // Variable found
        }
      }
      throw new TypeException("Variable with id "+id+" has not been declared");
    }

    //why are these methods static in the book?
    public FunType lookupFun(String id) {
      if (signatures.containsKey(id)) {
        return signatures.get(id);
      } else {
        throw new TypeException("Function with id \""+id+"\" has not been defined");
      }
    }

    public void removeVar(String id){
      contexts.get(0).remove(id);
    }

    //add a variable declaration to the environment/context
    public void updateVar(String id, Type ty) {
      //put variable at the top of the hashmap
      if (contexts.isEmpty()){
        newBlock();
      }
      if (!contexts.get(0).containsKey(id)) {
        if (ty instanceof Type_void){
          throw new TypeException("Type of argument/variable can not be void");
        }
        contexts.get(0).put(id, ty);
      } else {
        throw new TypeException("Variable with id \""+id+"\" already exists.");
      }
    }

    //add a function definition to the environment
    public void updateFun(String id, FunType funType) {
      if (!signatures.containsKey(id)) {
        signatures.put(id, funType);
      } else {
        throw new TypeException("Function with id \""+id+"\" has already been defined");
      }
    }

    public void newBlock(){
      this.contexts.addFirst(new HashMap<>());
    }

    public void exitBlock(){
      this.contexts.pop();
    }


  }

  public Program typecheck(Program p) {
    Env env = new Env();
    ListDef annotatedDefs = new ListDef();

    //type check the function headers/signatures
    if (p instanceof PDefs){
      PDefs pDefs = (PDefs) p;
      for (Def def : pDefs.listdef_){
        if (def instanceof DFun){
          DFun dfun = (DFun) def;
          FunType funType = new FunType(dfun.type_,dfun.listarg_);
          env.updateFun(dfun.id_,funType);
        } else {
          //if definition is not a function definition, we need to throw an exception.
          throw new TypeException("Not a function definition");
        }
      }
      if (!env.signatures.containsKey("main")){
        throw new TypeException("No main function defined");
      }
      FunType main = env.lookupFun("main");
      if (!main.args.isEmpty()){
        throw new TypeException("Main function can not have any arguments");
      }
      if (!(main.type instanceof Type_int)){
        throw new TypeException("The return type of the main function has to be int");
      }

      //go over each function and its body. Type check the function body.
      for (Def def : pDefs.listdef_){
        //this environment stores the local context of the function, i.e. its argument list
        Env fEnv = env;
        DFun dfun = (DFun) def;
        //create a new block scope for the function. in this scope the variables in the argument list of the function will exist
        //they will not exist outside of this scope and will be removed eventually.
        fEnv.newBlock();
        fEnv.funType = dfun.type_;
        for (Arg arg : dfun.listarg_){
          ADecl aDecl = (ADecl) arg;
          fEnv.updateVar(aDecl.id_, aDecl.type_);
        }
        DFun annotatedDFun = (DFun) checkDef(def,env);
        annotatedDefs.add(annotatedDFun);
        fEnv.exitBlock();
      }
    } else {
      throw new TypeException("Must be of type PDef");
    }
    return new PDefs(annotatedDefs);
  }

  public Def checkDef(Def def, Env arg){
    DFun dFun = (DFun) def;
    ListStm annotatedListStm = new ListStm();
    for (Stm stm : dFun.liststm_){
      Stm annotatedStm = stm.accept(new CheckAnnotatedStm(),arg);
      annotatedListStm.add(annotatedStm);
    }
    return new DFun(dFun.type_,dFun.id_,dFun.listarg_,annotatedListStm);
  }


  public static class CheckStm implements Stm.Visitor<Env,Env> {

    public Env visit(SExp p, Env arg) {
      //as long as it can infer a type for the expression, then the statement is valid.
      p.exp_.accept(new InferAnnotatedExp(),arg);
      return arg;
    }

    @Override
    public Env visit(SDecls p, Env arg) {
      for (String id : p.listid_){
        //updateVar will fail if the id already exists. i.e. the declaration declares a variable that exists in the current scope.
        arg.updateVar(id,p.type_);
      }
      //why do we return the environment?
      return arg;
    }

    @Override
    public Env visit(SInit p, Env arg) {

      //this is necessary. the only issue is that we need it as long as we do the infer exp.
      arg.updateVar(p.id_, p.type_);
      //check that the expression has a valid type
      Type t = p.exp_.accept(new InferExpType(),arg);
      //remove the variable from the contexts. This is necessary so that we can add it again.
      arg.removeVar(p.id_);

      //the if statement checks that the type of the expression is the same type as the variable. this is necessary.
      if (t.equals(p.type_) || typeCode(p.type_).equals(TypeCode.CDouble) && typeCode(t).equals(TypeCode.CInt)) {
        //this check will also fail if the variable id has already been defined in the same context.
        arg.updateVar(p.id_, p.type_);
      } else {
        //is this necessary. not mentioned in the book?
        throw new TypeException("The type of the expression does not match the type of the variable");
      }
      return arg;
    }

    @Override
    public Env visit(SReturn p, Env arg) {
      //check if the statement returns an expression with a valid type
      Type rt = p.exp_.accept(new InferExpType(),arg);
      if (!rt.equals(arg.funType) && !(arg.funType instanceof Type_double && rt instanceof Type_int)){
        throw new TypeException("The return type "+rt.toString()+" of the return statement does not match the return type of the function");
      }
      return arg;
    }

    @Override
    public Env visit(SWhile p, Env arg) {
      Type t = p.exp_.accept(new InferExpType(),arg);
      if (typeCode(t).equals(TypeCode.CBool)){
        arg.newBlock();
        p.stm_.accept(this,arg);
        arg.exitBlock();
        return arg;
      }
      throw new TypeException("Condition in while loop must be of type bool");
    }

    @Override
    public Env visit(SBlock p, Env arg) {
      arg.newBlock();
      for (Stm stm : p.liststm_){
        //check the statements using the new environment, which has the block scope as its top-most context
        //the other statements are checked using their regular environment.
        stm.accept(new CheckStm(),arg);
      }
      arg.exitBlock();
      return arg;
    }

    @Override
    public Env visit(SIfElse p, Env arg) {
      Type t = p.exp_.accept(new InferExpType(),arg);
      if (typeCode(t).equals(TypeCode.CBool)){
        arg.newBlock();
        //type check statement 1 in a new block
        p.stm_1.accept(this,arg);
        arg.exitBlock();
        arg.newBlock();
        //type check statement 2 in a new block.
        p.stm_2.accept(this,arg);
        arg.exitBlock();
        return arg;
      } else {
        throw new TypeException("Condition in if-else statement must be of type bool");
      }
    }
  }



  public static class CheckAnnotatedStm implements Stm.Visitor<Stm,Env> {

    public Stm visit(SExp p, Env arg) {
      //as long as it can infer a type for the expression, then the statement is valid.
      SExp sExp = new SExp(p.exp_.accept(new InferAnnotatedExp(),arg));
      return sExp;
    }

    @Override
    public Stm visit(SDecls p, Env arg) {
      for (String id : p.listid_){
        //updateVar will fail if the id already exists. i.e. the declaration declares a variable that exists in the current scope.
        arg.updateVar(id,p.type_);
      }
      //why do we return the environment?
      return p;
    }

    @Override
    public Stm visit(SInit p, Env arg) {
      //this is necessary. the only issue is that we need it as long as we do the infer exp.
      arg.updateVar(p.id_, p.type_);
      //check that the expression has a valid type
      Type t = p.exp_.accept(new InferExpType(),arg);
      //remove the variable from the contexts. This is necessary so that we can add it again.
      arg.removeVar(p.id_);

      //the if statement checks that the type of the expression is the same type as the variable. this is necessary.
      if (t.equals(p.type_) || typeCode(p.type_).equals(TypeCode.CDouble) && typeCode(t).equals(TypeCode.CInt)) {
        //this check will also fail if the variable id has already been defined in the same context.
        arg.updateVar(p.id_, p.type_);
      } else {
        //is this necessary. not mentioned in the book?
        throw new TypeException("The type of the expression does not match the type of the variable");
      }
      //the previous code just typechecks it. this code returns a new type annotated statement.
      ETyped eTyped = (ETyped) p.exp_.accept(new InferAnnotatedExp(),arg);
      //return a new SInit, but with the only difference that it is type annotated
      return new SInit(p.type_,p.id_,eTyped);
    }

    @Override
    public Stm visit(SReturn p, Env arg) {
      //check if the statement returns an expression with a valid type
      Type rt = p.exp_.accept(new InferExpType(),arg);
      if (!rt.equals(arg.funType) && !(arg.funType instanceof Type_double && rt instanceof Type_int)){
        throw new TypeException("The return type "+rt.toString()+" of the return statement does not match the return type of the function");
      }
      ETyped eTyped = (ETyped) p.exp_.accept(new InferAnnotatedExp(),arg);
      return new SReturn(eTyped);
    }

    @Override
    public Stm visit(SWhile p, Env arg) {
      Type t = p.exp_.accept(new InferExpType(),arg);
      if (typeCode(t).equals(TypeCode.CBool)){
        arg.newBlock();
        Stm annotatedStm = p.stm_.accept(this,arg);
        arg.exitBlock();
        Exp annotatedCondition = p.exp_.accept(new InferAnnotatedExp(),arg);
        return new SWhile(annotatedCondition,annotatedStm);
      }
      throw new TypeException("Condition in while loop must be of type bool");
    }

    @Override
    public Stm visit(SBlock p, Env arg) {
      ListStm stms = new ListStm();
      arg.newBlock();
      for (Stm stm : p.liststm_){
        //check the statements using the new environment, which has the block scope as its top-most context
        //the other statements are checked using their regular environment.
        Stm annotatedBlockStm = stm.accept(this,arg);
        stms.add(annotatedBlockStm);
      }
      arg.exitBlock();
      return new SBlock(stms);
    }

    @Override
    public Stm visit(SIfElse p, Env arg) {
      Type t = p.exp_.accept(new InferExpType(),arg);
      if (typeCode(t).equals(TypeCode.CBool)){
        arg.newBlock();
        //type check statement 1 in a new block
        Stm annotatedStm1 = p.stm_1.accept(this,arg);
        arg.exitBlock();
        arg.newBlock();
        //type check statement 2 in a new block.
        Stm annotatedStm2 = p.stm_2.accept(this,arg);
        arg.exitBlock();
        Exp annotatedExp = p.exp_.accept(new InferAnnotatedExp(),arg);
        return new SIfElse(annotatedExp,annotatedStm1,annotatedStm2);
      } else {
        throw new TypeException("Condition in if-else statement must be of type bool");
      }
    }
  }



  //checking different statements
  public static class InferExpType implements Exp.Visitor<Type,Env> {
    @Override
    public Type visit(EBool p, Env arg) {
      return new Type_bool();
    }

    public Type visit(EInt p, Env arg) {
      return new Type_int();
    }

    @Override
    public Type visit(EDouble p, Env arg) {
      return new Type_double();
    }

    @Override
    public Type visit(EId p, Env arg) {
      return arg.lookupVar(p.id_);
    }

    //function call
    @Override
    public Type visit(EApp p, Env arg) {
      ListArg listArg = arg.lookupFun(p.id_).args;
      ListExp listExp = p.listexp_;
      if (listArg.size() != listExp.size()){
        //Type checker checks that function call has same number of arguments as function parameters.
        throw new TypeException("The function call must have the same number of arguments as the function definition");
      }
      int len = listExp.size();
      for (int i=0;i<len;i++){
        ADecl aDecl = (ADecl) listArg.get(i);
        Exp exp = listExp.get(i);
        Type argType = aDecl.type_;
        Type expType = exp.accept(new InferExpType(),arg);
        if (!argType.equals(expType) && !(argType.equals(new Type_double()) && expType.equals(new Type_int()))){
          throw new TypeException("Function argument and expression must have the same type. Exception: Int can be cast to double.");
        }
      }
      return arg.lookupFun(p.id_).type;
    }

    @Override
    public Type visit(EPost p, Env arg) {
      Type t = arg.lookupVar(p.id_);
      if (typeCode(t).equals(TypeCode.CInt) || typeCode(t).equals(TypeCode.CDouble)) {
        return t;
      } else {
        throw new TypeException("Operand must be of type int or double");
      }
    }

    @Override
    public Type visit(EPre p, Env arg) {
      Type t = arg.lookupVar(p.id_);
      if (typeCode(t).equals(TypeCode.CInt) || typeCode(t).equals(TypeCode.CDouble)) {
        return t;
      } else {
        throw new TypeException("Operand must be of type int or double");
      }
    }

    @Override
    public Type visit(EMul p, Env arg) {
      Type t1 = p.exp_1.accept(this,arg);
      Type t2 = p.exp_2.accept(this,arg);
      if ((t1 instanceof Type_double || t1 instanceof Type_int) && (t2 instanceof Type_double || t2 instanceof Type_int)){
        if (t1.equals(t2)) {
          return t1;
        } else {
          return new Type_double();
        }
      }
      throw new TypeException("Operands to * must be of type int or double");
    }

    public Type visit(EAdd p, Env env) {
      Type t1 = p.exp_1.accept(this,env);
      Type t2 = p.exp_2.accept(this,env);
      if ((t1 instanceof Type_double || t1 instanceof Type_int) && (t2 instanceof Type_double || t2 instanceof Type_int)){
        if (t1.equals(t2)){
          return t1;
        } else {
          return new Type_double();
        }
      }
      throw new TypeException("Operands to + must be of type int or double");
    }

    @Override
    public Type visit(ECmp p, Env arg) {
      Type t1 = p.exp_1.accept(this,arg);
      Type t2 = p.exp_2.accept(this,arg);

      if ((t1 instanceof Type_double || t1 instanceof Type_int) && (t2 instanceof Type_double || t2 instanceof Type_int)){
        return new Type_bool();
      }
      if (p.cmpop_ instanceof OEq || p.cmpop_ instanceof ONEq){
        if (t1 instanceof Type_bool && t2 instanceof Type_bool){
          return new Type_bool();
        } else {
          throw new TypeException("Operands to == and != must be of type int, double or bool");
        }
      }
      throw new TypeException("Operands to comparison must be int or double");
    }

    @Override
    public Type visit(EAnd p, Env arg) {
      Type t1 = p.exp_1.accept(this,arg);
      Type t2 = p.exp_2.accept(this,arg);
      if (typeCode(t1).equals(TypeCode.CBool) && typeCode(t2).equals(TypeCode.CBool)){
        return new Type_bool();
      }
      throw new TypeException("Both operands to && must be of type bool");
    }

    @Override
    public Type visit(EOr p, Env arg) {
      Type t1 = p.exp_1.accept(this,arg);
      Type t2 = p.exp_2.accept(this,arg);
      if (typeCode(t1).equals(TypeCode.CBool) && typeCode(t2).equals(TypeCode.CBool)){
        return new Type_bool();
      }
      throw new TypeException("Both operands to || must be of type bool");
    }

    @Override
    public Type visit(EAss p, Env arg) {
      Type expType = p.exp_.accept(this,arg);
      if (arg.lookupVar(p.id_).equals(expType) || arg.lookupVar(p.id_).equals(new Type_double()) && expType.equals(new Type_int())){
        return arg.lookupVar(p.id_);
      } else {
        throw new TypeException("Expression must have the same type as the variable "+p.id_);
      }
    }

    @Override
    public Type visit(ETyped p, Env arg) {
      return p.type_;
    }

  }

  public static class InferAnnotatedExp implements Exp.Visitor<ETyped,Env>{

    @Override
    public ETyped visit(EBool p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EInt p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EDouble p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EId p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EApp p, Env arg) {
      ListExp annotatedListExp = new ListExp();
      for (Exp exp : p.listexp_){
        Exp annotatedExp = exp.accept(this,arg);
        annotatedListExp.add(annotatedExp);
      }
      //all the expressions/arguments of the function call will now be annotated
      EApp annotatedP = new EApp(p.id_,annotatedListExp);
      //return the type annotated expression call with the annotated arguments.
      return new ETyped(annotatedP,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EPost p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EPre p, Env arg) {
      return new ETyped(p,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EMul p, Env arg) {
      ETyped a = new ETyped(p.exp_1.accept(this,arg),p.exp_1.accept(new InferExpType(),arg));
      ETyped b = new ETyped(p.exp_2.accept(this,arg),p.exp_2.accept(new InferExpType(),arg));
        return new ETyped(new EMul(a, p.mulop_, b), p.accept(new InferExpType(), arg));

    }

    @Override
    public ETyped visit(EAdd p, Env arg) {
      ETyped a = new ETyped(p.exp_1.accept(this,arg),p.exp_1.accept(new InferExpType(),arg));
      ETyped b = new ETyped(p.exp_2.accept(this,arg),p.exp_2.accept(new InferExpType(),arg));
      return new ETyped(new EAdd(a, p.addop_, b), p.accept(new InferExpType(), arg));
    }

    @Override
    public ETyped visit(ECmp p, Env arg) {
      ETyped a = new ETyped(p.exp_1.accept(this,arg),p.exp_1.accept(new InferExpType(),arg));
      ETyped b = new ETyped(p.exp_2.accept(this,arg),p.exp_2.accept(new InferExpType(),arg));
      return new ETyped(new ECmp(a,p.cmpop_,b),p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EAnd p, Env arg) {
      ETyped a = new ETyped(p.exp_1.accept(this,arg),p.exp_1.accept(new InferExpType(),arg));
      ETyped b = new ETyped(p.exp_2.accept(this,arg),p.exp_2.accept(new InferExpType(),arg));
      return new ETyped(new EAnd(a,b),p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EOr p, Env arg) {
      ETyped a = new ETyped(p.exp_1.accept(this,arg),p.exp_1.accept(new InferExpType(),arg));
      ETyped b = new ETyped(p.exp_2.accept(this,arg),p.exp_2.accept(new InferExpType(),arg));
      return new ETyped(new EOr(a,b),p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(EAss p, Env arg) {
      ETyped expAnnotated = p.exp_.accept(this,arg);
      //annotate the expression of the assignment, i.e the right hand side of the equal sign. this is necessary as this is also an expression
      EAss pAnnotated = new EAss(p.id_,expAnnotated);
      //annotate the entire assignment expression
      return new ETyped(pAnnotated,p.accept(new InferExpType(),arg));
    }

    @Override
    public ETyped visit(ETyped p, Env arg) {
      return p;
    }

  }


}
