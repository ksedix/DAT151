import java.lang.constant.ClassDesc;
import java.util.*;
import cmm.Absyn.*;

public class Compiler
{

  public static class FunType{
    private Type returnType;
    private ListArg arguments;
    private String funType;

    public FunType(Type returnType, ListArg args){
      this.returnType = returnType;
      this.arguments = args;
    }

    public FunType(String funType){
      this.funType = funType;
    }

    //give the function type in JVM notation, so that it can be used in machine code instructions
    public String funTypeJVM(){
      String argumentTypes = "";
      for (Arg arg : arguments){
        ADecl aDecl = (ADecl) arg;
        argumentTypes += aDecl.type_.accept(new FunTypeVisitor(),null);
      }
      return "("+argumentTypes+")"+returnType.accept(new FunTypeVisitor(),null);
    }

    public String getFunType(){
      return funType;
    }

    public Type getReturnType(){
      return returnType;
    }

  }

  //The compiler environment
  public static class Env{

    public Type returnType;
    public HashMap<String,FunType> funTypes = new HashMap<>();
    public LinkedList<HashMap<String,Integer>> addresses = new LinkedList<>();
    public LinkedList<HashMap<String,Type>> varTypes = new LinkedList<>();
    int counterVAddresses = 0;
    int counterJumpLabels = 0;


    public Env(){
/*      funTypes.put("printInt",new FunType("(I)V"));
      funTypes.put("printDouble",new FunType("(D)V"));
      funTypes.put("readInt",new FunType("()I"));
      funTypes.put("readDouble",new FunType("()D"));*/
      ListArg printIntArgs = new ListArg();
      ListArg printDoubleArgs = new ListArg();
      printIntArgs.add(new ADecl(new Type_int(),"n"));
      printDoubleArgs.add(new ADecl(new Type_double(),"x"));
      funTypes.put("printInt",new FunType(new Type_void(),printIntArgs));
      funTypes.put("printDouble",new FunType(new Type_void(),printDoubleArgs));
      funTypes.put("readInt",new FunType(new Type_int(),new ListArg()));
      funTypes.put("readDouble",new FunType(new Type_double(),new ListArg()));
    }

    public Integer lookupVar(String id){
      for (HashMap<String,Integer> hm : addresses){
        if (hm.containsKey(id)){
          return hm.get(id);
        }
      }
      return null;
    }

    public Type lookupVarType(String id){
      for (HashMap<String,Type> hm : varTypes){
        if (hm.containsKey(id)){
          return hm.get(id);
        }
      }
      return null;
    }

    public FunType lookupFun(String id){
      return funTypes.get(id);
    }

    public void extend(DFun d){
      FunType funType = new FunType(d.type_, d.listarg_);
      funTypes.put(d.id_, funType);
    }

    public void extend(String id, Type t){
      if (addresses.isEmpty()){
        addresses.add(new HashMap<>());
      }
      if (varTypes.isEmpty()){
        varTypes.add(new HashMap<>());
      }
      //put the variable as well as its memory address in the hashmap. put it in the hashmap at the top-most context
      //this allows multiple variables with the same name to be stored in different addresses.
      addresses.get(0).put(id,counterVAddresses);
      varTypes.get(0).put(id,t);
      if (t instanceof Type_int || t instanceof Type_bool){
        counterVAddresses += 1;
      } else {
        counterVAddresses += 2;
      }
    }

    public String newLabel(){
      String rv = "L"+counterJumpLabels;
      counterJumpLabels+=1;
      return rv;
    }

    public void newBlock(){
      addresses.addFirst(new HashMap<>());
      varTypes.addFirst(new HashMap<>());
    }
    public void exitBlock(){
      addresses.pop();
      varTypes.pop();
    }

    public Type getReturnType() {
      return returnType;
    }
  }

  public static class FunTypeVisitor implements Type.Visitor<String,Object>{

    @Override
    public String visit(Type_bool p, Object arg) {
      return "Z";
    }

    @Override
    public String visit(Type_int p, Object arg) {
      return "I";
    }

    @Override
    public String visit(Type_double p, Object arg) {
      return "D";
    }

    @Override
    public String visit(Type_void p, Object arg) {
      return "V";
    }
  }

  public static enum TypeCode {CInt, CDouble, CBool, CVoid}

  //correct
  public static TypeCode typeCode (Type ty){
    return ty.accept(new TypeCodeVisitor(),null);
  }

  public static class TypeCodeVisitor implements Type.Visitor<TypeCode,Object>{

    @Override
    public TypeCode visit(Type_bool p, Object arg) {
      return TypeCode.CBool;
    }

    @Override
    public TypeCode visit(Type_int p, Object arg) {
      return TypeCode.CInt;
    }

    @Override
    public TypeCode visit(Type_double p, Object arg) {
      return TypeCode.CDouble;
    }

    @Override
    public TypeCode visit(Type_void p, Object arg) {
      return TypeCode.CVoid;
    }
  }

  private class CompileStm implements Stm.Visitor<Object,Env>{


    @Override
    public Object visit(SExp p, Env arg) {
      p.exp_.accept(new CompileExp(),arg);
      ETyped eTyped = (ETyped) p.exp_;
      if (eTyped.type_ instanceof Type_int || eTyped.type_ instanceof Type_bool){
        //remove the return value of the expression from the top of the stack if the expression is used in a statement.
        emit("pop");
      } else if (eTyped.type_ instanceof Type_double) {
        emit("pop2");
      }
      return null;
    }

    @Override
    public Object visit(SDecls p, Env arg) {
      for (String id : p.listid_){
        arg.extend(id,p.type_);
      }
      return null;
    }

    @Override
    public Object visit(SInit p, Env arg) {
      arg.extend(p.id_,p.type_);
      Integer address = arg.lookupVar(p.id_);
      //get the value of the right hand side expression
      p.exp_.accept(new CompileExp(),arg);
      if (p.type_ instanceof Type_int || p.type_ instanceof Type_bool){
        //store the value in the variable memory address
        emit("istore "+address);
      } else {
        ETyped typedExp = (ETyped) p.exp_;
        if (typedExp.type_ instanceof Type_int){
          emit("i2d");
        }
        emit("dstore "+address);
      }
      return null;
    }

    @Override
    public Object visit(SReturn p, Env arg) {
      ETyped eTyped = (ETyped) p.exp_;
      Type returnType = arg.returnType;
      p.exp_.accept(new CompileExp(),arg);
      if (eTyped.type_ instanceof Type_bool){
        //the machine code instruction for returning an int value
        emit("ireturn");
      } else if (eTyped.type_ instanceof Type_int ) {
          if (returnType instanceof Type_double){
            emit("i2d");
            emit("dreturn");
          } else {
            emit("ireturn");
          }
      } else if (eTyped.type_ instanceof Type_double) {
        //the machine code instruction(Java bytecode) for returning a double value
        emit ("dreturn");
      } else {
        //return type void.
        emit("return");
      }
      return null;
    }

    @Override
    public Object visit(SWhile p, Env arg) {
      String startLabel = arg.newLabel();
      String endLabel = arg.newLabel();
      emit(startLabel+":");
      p.exp_.accept(new CompileExp(),arg);
      emit("ifeq "+endLabel);
      //do we need to add block-scope or is the statement of the while loop a block statement?
      arg.newBlock();
      p.stm_.accept(this,arg);
      arg.exitBlock();
      emit("goto "+startLabel);
      emit(endLabel+":");
      return null;
    }

    @Override
    public Object visit(SBlock p, Env arg) {
      arg.newBlock();
      for (Stm stm : p.liststm_){
        stm.accept(this,arg);
      }
      arg.exitBlock();
      return null;
    }

    @Override
    public Object visit(SIfElse p, Env arg) {
      String elseLabel = arg.newLabel();
      String endLabel = arg.newLabel();
      p.exp_.accept(new CompileExp(),arg);
      emit("ifeq "+elseLabel);
      arg.newBlock();
      p.stm_1.accept(this,arg);
      arg.exitBlock();
      emit("goto "+endLabel);
      emit(elseLabel+":");
      arg.newBlock();
      p.stm_2.accept(this,arg);
      arg.exitBlock();
      emit(endLabel+":");
      return null;
    }
  }

  private class CompileExp implements Exp.Visitor<Void,Env>{

    @Override
    public Void visit(EBool p, Env arg) {
      if (p.boollit_ instanceof LTrue){
        emit("iconst_1");
      } else {
        emit("iconst_0");
      }
      return null;
    }

    @Override
    public Void visit(EInt p, Env arg) {
      String intValue = p.integer_.toString();
      emit("ldc "+intValue);
      return null;
    }

    @Override
    public Void visit(EDouble p, Env arg) {
      String doubleValue = p.double_.toString();
      emit("ldc2_w "+doubleValue);
      return null;
    }

    @Override
    public Void visit(EId p, Env arg) {
      //ETyped eTyped = (ETyped) p; //fråga under handledning.
      Integer address = arg.lookupVar(p.id_);
      //we have to lookup var type since it is not given/possible to get with type annotations.
      Type t = arg.lookupVarType(p.id_);
      if (typeCode(t).equals(TypeCode.CInt) || typeCode(t).equals(TypeCode.CBool)) {
        emit("iload "+address);
      } else {
        emit("dload "+address);
      }
      return null;
    }

    @Override
    public Void visit(EApp p, Env arg) {
      FunType funType = arg.lookupFun(p.id_);
      String type = funType.funTypeJVM();
      //function call
      for (int i=0;i<p.listexp_.size();i++){
        ETyped eTyped = (ETyped) p.listexp_.get(i);
        ADecl aDecl = (ADecl) funType.arguments.get(i);
        Type pType = aDecl.type_;
        //Integer address = arg.lookupVar(aDecl.id_);
        //compile each expression argument and add it to the top of the stack
        eTyped.exp_.accept(this,arg);

        if (eTyped.type_ instanceof Type_int && pType instanceof Type_double){
          emit("i2d");
        }

      }

      if (p.id_.equals("readInt") || p.id_.equals("readDouble") || p.id_.equals("printInt") || p.id_.equals("printDouble")){
        emit("invokestatic Runtime/"+p.id_+type);
      } else {
        emit("invokestatic " + className + "/" + p.id_ + type);
      }
      //set the return type to the old return type. this is necessary in case a function called another function,
      //we want the return type of the parent function to come back.
      return null;
    }

    @Override
    public Void visit(EPost p, Env arg) {
      //get the variable memory address so we know which address to write the result to
      Integer address = arg.lookupVar(p.id_);
      //get the type of the variable so that we know if we to integer addition or double addition
      Type t = arg.lookupVarType(p.id_);
      if (t instanceof Type_int || t instanceof Type_bool) {
        if (p.incdecop_ instanceof OInc) {
          emit("iload " + address);
          emit("dup");
          emit("iconst_1");
          emit("iadd");
          emit("istore " + address);
        } else {
          emit("iload " + address);
          emit("dup");
          emit("iconst_1");
          emit("isub");
          emit("istore " + address);
        }
      } else {
        if (p.incdecop_ instanceof OInc) {
          emit("dload " + address);
          emit("dup2");
          emit("dconst_1");
          emit("dadd");
          emit("dstore " + address);
        } else {
          emit("dload " + address);
          emit("dup2");
          emit("dconst_1");
          emit("dsub");
          emit("dstore " + address);
        }
      }
      return null;
    }

    @Override
    public Void visit(EPre p, Env arg) {
      Integer address = arg.lookupVar(p.id_);
      Type t = arg.lookupVarType(p.id_);
      if (t instanceof Type_int || t instanceof Type_bool) {
        if (p.incdecop_ instanceof OInc) {
          emit("iload " + address);
          emit("iconst_1");
          emit("iadd");
          //store the result on the stack for further operations
          emit("dup");
          emit("istore " + address);
        } else {
          emit("iload " + address);
          emit("iconst_1");
          emit("isub");
          //store the result on the stack for further operations
          emit("dup");
          emit("istore " + address);
        }
      } else {
        if (p.incdecop_ instanceof OInc) {
          emit("dload " + address);
          emit("dconst_1");
          emit("dadd");
          emit("dup2");
          emit("dstore " + address);
        } else {
          emit("dload " + address);
          emit("dconst_1");
          emit("dsub");
          emit("dup2");
          emit("dstore " + address);
        }
      }
      return null;
    }

    @Override
    public Void visit(EMul p, Env arg) {
      ETyped eTyped1 = (ETyped) p.exp_1;
      ETyped eTyped2 = (ETyped) p.exp_2;

      if (eTyped1.type_ instanceof Type_int && eTyped2.type_ instanceof Type_int){
        //compile expression 1
        p.exp_1.accept(this,arg);
        //compile expression 2
        p.exp_2.accept(this,arg);
        if (p.mulop_ instanceof OTimes) {
          emit("imul");
        } else {
          emit("idiv");
        }
      } else {
        p.exp_1.accept(this,arg);
        if (eTyped1.type_ instanceof Type_int){
          emit("i2d");
        }
        p.exp_2.accept(this,arg);
        if (eTyped2.type_ instanceof Type_int){
          emit("i2d");
        }
        if (p.mulop_ instanceof OTimes){
          emit("dmul");
        } else {
          emit("ddiv");
        }
      }

      return null;

    }

    @Override
    public Void visit(EAdd p, Env arg) {

      ETyped exp1 = (ETyped) p.exp_1;
      ETyped exp2 = (ETyped) p.exp_2;

      if (typeCode(exp1.type_).equals(TypeCode.CInt) && typeCode(exp2.type_).equals(TypeCode.CInt)){
        p.exp_1.accept(this,arg);
        p.exp_2.accept(this,arg);
        if (p.addop_ instanceof OPlus) {
          emit("iadd");
        } else {
          emit("isub");
        }
      } else {
        p.exp_1.accept(this,arg);
        if (exp1.type_ instanceof Type_int){
          emit("i2d");
        }
        p.exp_2.accept(this,arg);
        if (exp2.type_ instanceof Type_int){
          emit("i2d");
        }
        if (p.addop_ instanceof OPlus) {
          emit("dadd");
        } else {
          emit("dsub");
        }
      }
      return null;
    }

    @Override
    public Void visit(ECmp p, Env arg) {
      String trueLabel = arg.newLabel();
      String endLabel = arg.newLabel();
      ETyped exp1 = (ETyped) p.exp_1;
      ETyped exp2 = (ETyped) p.exp_2;

      if ((exp1.type_ instanceof Type_int && exp2.type_ instanceof Type_int) || (exp1.type_ instanceof Type_bool && exp2.type_ instanceof Type_bool)) {
        p.exp_1.accept(this, arg);
        p.exp_2.accept(this, arg);
        if (p.cmpop_ instanceof OEq) {
          emit("if_icmpeq "+trueLabel);
        } else if (p.cmpop_ instanceof ONEq) {
          emit("if_icmpne "+trueLabel);
        } else if (p.cmpop_ instanceof OLt) {
          emit("if_icmplt "+trueLabel);
        } else if (p.cmpop_ instanceof OGt) {
          emit("if_icmpgt "+trueLabel);
        } else if (p.cmpop_ instanceof OGtEq) {
          emit("if_icmpge "+trueLabel);
          emit("iconst_0");
          emit("goto "+endLabel);
        } else if (p.cmpop_ instanceof OLtEq) {
          emit("if_icmple "+trueLabel);
        }
      } else {
        p.exp_1.accept(new CompileExp(),arg);
        if (exp1.type_ instanceof Type_int){
          emit("i2d");
        }
        p.exp_2.accept(new CompileExp(),arg);
        if (exp2.type_ instanceof Type_int){
          emit("i2d");
        }
        emit("dcmpg");
        if (p.cmpop_ instanceof OEq) {
          emit("ifeq "+trueLabel);
        } else if (p.cmpop_ instanceof ONEq) {
          emit("ifne "+trueLabel);
        } else if (p.cmpop_ instanceof OLt) {
          emit("iconst_m1");
          emit("if_icmpeq "+trueLabel);
        } else if (p.cmpop_ instanceof OGt) {
          emit("iconst_1");
          emit("if_icmpeq "+trueLabel);
        } else if (p.cmpop_ instanceof OGtEq) {
          emit("iconst_m1");
          emit("if_icmpne "+trueLabel);
        } else if (p.cmpop_ instanceof OLtEq) {
          emit("iconst_1");
          emit("if_icmpne "+trueLabel);
        }
      }
      emit("iconst_0");
      emit("goto "+endLabel);
      emit(trueLabel+":");
      emit("iconst_1");
      emit(endLabel+":");
      return null;
    }

    @Override
    public Void visit(EAnd p, Env arg) {
      String endLabel = arg.newLabel();
      String falseLabel = arg.newLabel();
      p.exp_1.accept(this,arg);
      emit("ifeq "+falseLabel);
      p.exp_2.accept(this,arg);
      emit("goto "+endLabel);
      p.exp_2.accept(this,arg);
      emit(falseLabel+":");
      emit("iconst_0");
      emit(endLabel+":");
      return null;
    }

    @Override
    public Void visit(EOr p, Env arg) {
      String endLabel = arg.newLabel();
      String falseLabel = arg.newLabel();
      p.exp_1.accept(this,arg);
      emit("ifeq "+falseLabel);
      emit("iconst_1");
      emit("goto "+endLabel);
      emit(falseLabel+":");
      p.exp_2.accept(this,arg);
      emit(endLabel+":");
      return null;
    }

    @Override
    public Void visit(EAss p, Env arg) {
      p.exp_.accept(this,arg);
      ETyped exp = (ETyped) p.exp_;
      Integer address = arg.lookupVar(p.id_);
      if (typeCode(exp.type_).equals(TypeCode.CBool)){
        emit("dup");
        //lookupVar gives you the integer memory location of the variable from the scope.
        emit("istore "+address);
      } else if (typeCode(exp.type_).equals(TypeCode.CInt)){
        if (arg.lookupVarType(p.id_) instanceof Type_double){
          emit("i2d");
          emit("dup2");
          emit("dstore "+address);
        } else {
          emit("dup");
          emit("istore "+address);
        }
      } else {
        emit("dup2");
        emit("dstore "+address);
      }
      return null;
    }

    @Override
    public Void visit(ETyped p, Env arg) {
      p.exp_.accept(this,arg);
      return null;
    }

  }

  public boolean hasReturnStatement(DFun dFun){
    for (Stm stm : dFun.liststm_){
      if (stm instanceof SReturn){
        return true;
      }
    }
    return false;
  }

  public void compile(Exp e, Env env){
    e.accept(new CompileExp(),env);
  }
  public void compile(Stm stm,Env arg){
    stm.accept(new CompileStm(),arg);
  }

  public void compile(Def d,Env env){
    DFun dFun = (DFun) d;
    env.counterVAddresses = 0;
    FunType funType = env.lookupFun(dFun.id_);
    env.returnType = funType.getReturnType();
    emit(".method public static "+dFun.id_+funType.funTypeJVM());
    //we use an upper bound here instead of specific values. How to calculate specific values for each function?
    emit(".limit locals 1000");
    emit(".limit stack 1000");
    //enter a new block because the function should be evaluated in a new block.

    env.newBlock();

    //extend environment with variables.
    for (Arg arg : dFun.listarg_){
      ADecl aDecl = (ADecl) arg;
      env.extend(aDecl.id_,aDecl.type_);
    }

    for (Stm stm : dFun.liststm_){
      stm.accept(new CompileStm(),env);
    }

    env.exitBlock();

    if (dFun.type_ instanceof Type_void) {
      //return void from the method. this should be placed in the case no return statement was in the void returning function.
      //how to know if no return statement was in the void returning function?
      if (!hasReturnStatement(dFun)) {
        //return if no explicit return statement in the void function.
        emit("return");
      }
    }
    if (dFun.id_.equals("main")){
      if (!hasReturnStatement(dFun)){
        emit("iconst_0");
        emit("ireturn");
      }
    }
    //check if the main function is missing a return statement. main does not have to have a return statement according to lab2 description.
    emit(".end method");
  }
  public void emit(String c){
    //this is correct. it writes the machine code to the output linked list.
    output.add(c+"\n");
  }

  Env env = new Env();
  String className;

  // The output of the compiler is a list of strings.
  LinkedList<String> output;

  // Compile C-- AST to a .j source file (returned as String).
  // name should be just the class name without file extension.
  public String compile(String name, cmm.Absyn.Program p) {
    className = name;
    // Initialize output
    output = new LinkedList();

    // Output boilerplate
    output.add(".class public " + name + "\n");
    output.add(".super java/lang/Object\n");
    output.add("\n");
    output.add(".method public <init>()V\n");
    output.add("  .limit locals 1\n");
    output.add("\n");
    output.add("  aload_0\n");
    output.add("  invokespecial java/lang/Object/<init>()V\n");
    output.add("  return\n");
    output.add("\n");
    output.add(".end method\n");
    output.add("\n");
    output.add(".method public static main([Ljava/lang/String;)V\n");
    output.add("  .limit locals 1\n");
    output.add("  .limit stack  1\n");
    output.add("\n");
    output.add("  invokestatic " + name + "/main()I\n");
    output.add("  pop\n");
    output.add("  return\n");
    output.add("\n");
    output.add(".end method\n");
    output.add("\n");

    // TODO: compile AST, appending to output.
    PDefs pDefs = (PDefs) p;

    //extend environment first
    for (Def d : pDefs.listdef_){
      DFun dFun = (DFun) d;
      //extend environment with function definitions. This is necessary so that all parts of the code knows of all other parts before we start compiling.
      env.extend(dFun);
    }

    //compile each function later.
    for (Def d : pDefs.listdef_){
      compile(d,env);
    }

    // Concatenate strings in output to .j file content.
    StringBuilder jtext = new StringBuilder();
    for (String s: output) {
      jtext.append(s);
    }
    return jtext.toString();
  }
}
