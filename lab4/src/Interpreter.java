import java.util.*;
import fun.Absyn.*;

public class Interpreter {

  final Strategy strategy;

  public Interpreter(Strategy strategy) {
    this.strategy = strategy;
  }

  public EAbs recursiveAbs(ListIdent listident,Exp e){
    //base case
    if (listident.size()==1){
      return new EAbs(listident.get(0),e);
    }
    String argument = listident.get(0);
    listident.pop();
    return new EAbs(argument,recursiveAbs(listident,e));
  }

  public void interpret(Program p) {
    Env env = new Env();
//    throw new RuntimeException("Interpreter not implemented yet");
    Prog prog = (Prog) p;
    //update the environment with the function definitions
    for (Def def : prog.listdef_){
      DDef fDef = (DDef) def;
      Env emptyEnv = new Env();
      if (fDef.listident_.size()>0){
        EAbs lambdaAbstract = recursiveAbs(fDef.listident_, fDef.exp_);
        env.updateFun(fDef.ident_, new Value(lambdaAbstract,emptyEnv));
      } else {
        //in case the function does not take any arguments. Ex: quadruple = twice double
        env.updateFun(fDef.ident_, new Value(fDef.exp_,emptyEnv));
      }
    }

    DMain dMain = (DMain) prog.main_;
    Integer value = dMain.exp_.accept(new ExpValue(), env).value;
    if (value == null){
      throw new RuntimeException("Expression does not evaluate to an Integer");
    }
    System.out.println(value);

  }

  //A value represents a closure, i.e. an expression with an environment that closes any free variables
  //A value can also be a integer literal
  private class Value {
    private Integer value;
    private Exp e;
    private Env env;

    //A value that is a closed expression
    public Value(Exp e, Env env) {
      this.e = e;
      this.env = env;
    }

    //A value that is an integer literal
    public Value(Integer integer,Env env){
      this.value = integer;
      this.env = env;
    }

    public Integer getValue(){
      return value;
    }

  }

  private class Env {
    //storage for variables
    private HashMap<String,Value> variables;
    //storage for functions
    private HashMap<String,Value> functions;

    public Env(){
      variables = new HashMap<>();
      functions = new HashMap<>();
    }

    public Env(Env env){
      this.variables = new HashMap<>(env.variables);
      this.functions = new HashMap<>(env.functions);
    }

    public Env(HashMap<String,Value> variables){
      this.variables = new HashMap<>(variables);
      functions = new HashMap<>();
    }

    public Env(HashMap<String,Value> functions, HashMap<String,Value> variables){
      this.functions = new HashMap<>(functions);
      this.variables = new HashMap<>(variables);
    }

    public Value lookupVar(String id){
      return variables.get(id);
    }

    public Value lookupFun(String id){
      return functions.get(id);
    }

    //add a new closed expression to the environment
    public void updateVar(String id,Value value){
      variables.put(id,value);
    }
    public void updateFun(String id, Value value){
      functions.put(id,value);
    }

  }


  private class ExpValue implements Exp.Visitor<Value, Env> {

    @Override
    public Value visit(EVar p, Env arg) {
      //look for the value in variable storage first
      Value value = arg.lookupVar(p.ident_);
      //if the value is a function symbol
      if (value == null){
        Value funVal = arg.lookupFun(p.ident_);
        Env env = new Env(arg.functions,funVal.env.variables);
        return funVal.e.accept(this,env);
      }
      Env env = new Env(arg.functions,value.env.variables);
      if (value.value == null){
        return value.e.accept(this,env);
      }
      return value;
    }

    @Override
    public Value visit(EInt p, Env arg) {
      return new Value(p.integer_,arg);
    }

    @Override
    public Value visit(EApp p, Env arg) {
      Value val = p.exp_1.accept(this,arg);
      EAbs abstraction = (EAbs) val.e;
      Value argVal;
      if (strategy == Strategy.CallByValue){
        argVal = p.exp_2.accept(this,arg);
      } else {
        argVal = new Value(p.exp_2,new Env(arg.variables));
      }
      Env env = new Env(arg.functions,val.env.variables);
      env.updateVar(abstraction.ident_,argVal);
      return abstraction.exp_.accept(this,env);
    }

    @Override
    public Value visit(EAdd p, Env arg) {
      Value val1 = p.exp_1.accept(this,arg);
      Value val2 = p.exp_2.accept(this,arg);
      return new Value(val1.getValue()+val2.getValue(),arg);
    }

    @Override
    public Value visit(ESub p, Env arg) {
      Value val1 = p.exp_1.accept(this,arg);
      Value val2 = p.exp_2.accept(this,arg);
      return new Value(val1.getValue() - val2.getValue(),arg);
    }

    @Override
    public Value visit(ELt p, Env arg) {
      Value value1 = p.exp_1.accept(this,arg);
      Value value2 = p.exp_2.accept(this,arg);
      if (value1.getValue().compareTo(value2.getValue())<0){
        return new Value(1,arg);
      } else {
        return new Value(0,arg);
      }
    }

    @Override
    public Value visit(EIf p, Env arg) {
      Value condition = p.exp_1.accept(this,arg);
      //lazy evaluation
      if (condition.value == 1){
        return p.exp_2.accept(this,arg);
      } else {
        return p.exp_3.accept(this,arg);
      }
    }

    @Override
    public Value visit(EAbs p, Env arg) {
      //a closure with the values of the current environment
      return new Value(p,new Env(arg.variables));
    }


  }
}
