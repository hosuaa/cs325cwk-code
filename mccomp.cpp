#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floatingpoint Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floatingpoint Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

//root of ast tree - the program. will contain the overall return value
class AST {
public:
  virtual ~AST() {}
  //virtual Value *codegen() = 0;
  //virtual std::string to_string() const {};
};
//program is a list of statements
class Statement : public AST {
public:
  virtual ~Statement() {//: Tok(tok) {}
    //Tok = tok;
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//expressions have types and perform operations
class Expression : public AST {
  //Types Type; - semantics
  //TOKEN Tok;
public:
  virtual ~Expression() {} //Expression() : Type(Types::INT), Tok(CurTok) {}
  //Expression(Types type, TOKEN tok) {: Type(type), Tok(tok) {}
    //Type = type;
    //Tok = tok;
  //}
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//root of ast. 
class Program : public AST {
  //std::vector<AST*> Statements;
public:
  std::vector<Statement> Statements;
  Program() {
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//list of statements
class BlockClass : public Statement {
  std::vector<Statement> Statements; //each statement is a node, adjacent elements in the list are directly connected in the ast
public:
  BlockClass(std::vector<Statement> statements) {//: Statements(statements), Tok(tok) {}
    Statements = std::move(statements);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//if statements have 3 components - the comparison after the if, and 2 statements blocks : 1 if its true and 1 if its false.
//Both statement blocks can optionally be null (e.g the expression in the if executes code and the statement blocks are uneeded, or no else is given)
class IfThenElse : public Statement {
  std::unique_ptr<Expression> Cond; //condition?
  std::unique_ptr<BlockClass> Block1; //if cond then block1 else block2
  std::unique_ptr<BlockClass> Block2;
public:
  IfThenElse(std::unique_ptr<Expression> cond, std::unique_ptr<BlockClass> block1, std::unique_ptr<BlockClass> block2)  {//: Val(val), Tok(tok) {}
    Cond = std::move(cond);
    Block1 = std::move(block1);
    Block2 = std::move(block2);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//while has 2 components - the condition to exit the while loop and the block to execute
class WhileLoop : public Statement {
  std::unique_ptr<Expression> Cond; //condition?
  std::unique_ptr<BlockClass> Loop;
public:
  WhileLoop(std::unique_ptr<Expression> cond, std::unique_ptr<BlockClass> loop) {//: Val(val), Tok(tok) {}
    Cond = std::move(cond);
    Loop = std::move(loop);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//can only declare 1 variable a line (int a,b; not allowed) so a variable declaration is a statement - stores type?
//potentially unecessary
class Declaration : public Statement {
  std::string Name;
  std::string Type; //store type
public:
  Declaration(std::string type, std::string name) {//: Val(val), Tok(tok) {}
    Type = type;
    Name = name;
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};
class Variable : public Expression {
  std::string Name;

public:
  Variable(const std::string &Name) : Name(Name) {}
};
//no ++, --... so only consider = with a LHS and a RHS - LHS stores the value of the expression on the RHS
class Assignment : public Statement {
  TOKEN Tok;
  //std::unique_ptr<Expression> LHS, RHS;
  std::string Name;
public:
  Assignment(TOKEN tok, std::string name) {//: Val(val), Tok(tok) {}
    Tok = tok;
    Name = name;
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//first line of a function, also to handle extern
//type name args
class Prototype : public Statement {
  std::string Type;
  std::string Name;
  std::vector<Declaration> Args;

public:
  Prototype(std::string type, std::string name, std::vector<Declaration> args) {
    Type = type;
    Name = name;
    Args = std::move(args);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

//void functions are statements rather than expressions (since they return no value they just execute the block with the parameters given)
//made up of function prototype and statement block
class VoidFunction : public Statement {
  std::unique_ptr<Prototype> Proto;
  std::unique_ptr<BlockClass> Body;
public:
  VoidFunction(std::unique_ptr<Prototype> proto, std::unique_ptr<BlockClass> body) {//: Val(val), Tok(tok) {}
    Proto = std::move(proto);
    Body = std::move(body);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};
//a function consists of the prototype and the body (statement block) 
//non void so will return 
class Func : public Statement {
  //std::string Name;
  std::unique_ptr<Prototype> Proto;
  std::unique_ptr<BlockClass> Body;

public:
  Func(std::unique_ptr<Prototype> proto, std::unique_ptr<BlockClass> body) {//: Val(val), Tok(tok) {}
    Proto = std::move(proto);
    Body = std::move(body);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

class Literal : public Expression {
  std::string Name;
public:
  Literal(std::string name) {
    Name = name;
  }
};

//binary operations - LHS and RHS evaluated (recursively) on op
class BinaryOp : public Expression {
  //BinaryOp():Expression(Type, Tok);
  char Op;
  std::unique_ptr<Expression> LHS, RHS;

public:
  BinaryOp(char op, std::unique_ptr<Expression> lhs, std::unique_ptr<Expression> rhs) {//: Op(op), Tok(tok), LHS(std::move(lhs)), RHS(std::move(rhs)){}
    Op = op;
    LHS = std::move(lhs);
    RHS = std::move(rhs);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};
//unary operations - !(a||b) allowed
class UnaryOp : public Expression {
  char Op;
  std::unique_ptr<Expression> Expr;

public:
  UnaryOp(char op, std::unique_ptr<Expression> expr) {//: Op(op), Tok(tok), Expr(std::move(expr)){}
    Op = op;
    Expr = std::move(expr);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

class FunctionCall : public Expression {
  std::string Name;
  std::vector<Expression*> Params;

public:
  FunctionCall(std::string name, std::vector<Expression*> params) {//: Op(op), Tok(tok), Expr(std::move(expr)){}
    Name = name;
    Params = std::move(params);
  }
  //virtual Value *codegen() override;
  //virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};


//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */
// program ::= extern_list decl_list
static bool Expr(); //defined for ArgListPrime(), ArgList() and RvalUnary()
static bool ArgListPrime() {
  if (CurTok.type==COMMA) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (Expr()) {
      return ArgListPrime();
    }
  }
  return true;
}
static bool ArgList() {
  if (Expr()) {
    return ArgListPrime();
  }
  return false;
}
static bool Args() {
  if (ArgList()) {
    return true;
  }
  return true;
}
static bool RvalLit() {
  if (CurTok.type==INT_LIT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return true;
  } else if (CurTok.type==FLOAT_LIT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return true;
  } else if (CurTok.type==BOOL_LIT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
  }
  return false;
}
static bool RvalIdent() {
  if (CurTok.type==IDENT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (CurTok.type==LPAR) {
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (Args()) {
        if (CurTok.type==RPAR) {
          printf("%s ",CurTok.lexeme.c_str());
          CurTok = getNextToken();
          return true;
        }
      }
    }
    return true;
  }
  return RvalLit();
}
static bool RvalUnary() {
  if (CurTok.type==LPAR) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (Expr()) {
      if (CurTok.type==RPAR) {
        printf("%s ",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        return true;
      }
    }
  }
  return RvalIdent();
}
static bool RvalMult() {
  if (CurTok.type==MINUS || CurTok.type==NOT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
  }
  return RvalUnary();
}
static bool RvalAddPrime() {
  if (CurTok.type==ASTERIX || CurTok.type==DIV || CurTok.type==MOD) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalMult()) {
      return RvalAddPrime();
    }
  }
  return true;
}
static bool RvalAdd() {
  if (RvalMult()) {
    return RvalAddPrime();
  }
  return false;
}
static bool RvalCompPrime() {
  if (CurTok.type==PLUS || CurTok.type==MINUS) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalAdd()) {
      return RvalCompPrime();
    }
  }
  return true;
}
static bool RvalComp() {
  if (RvalAdd()) {
    return RvalCompPrime();
  }
  return false;
}
static bool RvalEqPrime() {
  if (CurTok.type==LE || CurTok.type==LT || CurTok.type==GE || CurTok.type==GT) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalComp()) {
      return RvalEqPrime();
    }
  }
  return true;
}
static bool RvalEq() {
  if (RvalComp()) {
    return RvalEqPrime();
  }
  return false;
}
static bool RvalAndPrime() {
  if (CurTok.type==EQ || CurTok.type==NE) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalEq()) {
      return RvalAndPrime();
    }
  }
  return true;
}
static bool RvalAnd() {
  if (RvalEq()) {
    return RvalAndPrime();
  }
  return false;
}
static bool RvalOrPrime() {
  if (CurTok.type==AND) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalAnd()) {
      return RvalOrPrime();
    }
  }
  return true;
}
static bool RvalOr() {
  if (RvalAnd()) {
    return RvalOrPrime();
  }
  return false;
}
static bool RvalPrime() {
  if (CurTok.type==OR) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (RvalOr()) {
      return RvalPrime();
    }
  }
  return true;
}
static bool Rval() {
  if (RvalOr()) {
    return RvalPrime();
  }
  return false;
}
static bool Expr() {
  TOKEN CurTokCopy = CurTok;
  CurTok = getNextToken();
  if (CurTokCopy.type==IDENT && CurTok.type==ASSIGN) { //lookahead to ensure IDENT rhs of expr is rval_ident (so it doesnt try result=a=... and does result=a+b)
    printf("%s ",CurTokCopy.lexeme.c_str());
    //putBackToken(CurTok);
    if (CurTok.type==ASSIGN) {
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      return Expr();
    }
  }
  putBackToken(CurTok);
  CurTok=CurTokCopy;
  return Rval();
}
static bool ReturnStmt(std::vector<Statement> block) {
  if (CurTok.type==RETURN) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (CurTok.type==SC) {
      printf("%s\n",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      return true;
    } else if (Expr()) {
      if (CurTok.type==SC) {
        printf("%s\n",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        return true;
      }
    }
  }
  return false;
}
static bool Block(std::vector<Statement> block); //define for ElseStmt(), IfStmt() and Stmt()
static bool ElseStmt(std::vector<Statement> block) {
  if (CurTok.type==ELSE) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return Block(block);
  }
  return true;
}
static bool IfStmt(std::vector<Statement> block) {
  if (CurTok.type==IF) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (CurTok.type==LPAR) {
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (Expr()) {
        if (CurTok.type==RPAR) {
          printf("%s ",CurTok.lexeme.c_str());
          CurTok = getNextToken();
          if (Block(block)) {
            return ElseStmt(block);
          }
        }
      }
    }
  }
  return false;
}
static bool Stmt(std::vector<Statement> block); //define for WhileStmt()
static bool WhileStmt(std::vector<Statement> block) {
  if (CurTok.type==WHILE) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (CurTok.type==LPAR) {
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (Expr()) {
        if (CurTok.type==RPAR) {
          printf("%s ",CurTok.lexeme.c_str());
          CurTok = getNextToken();
          return Stmt(block);
        }
      }
    }
  }
  return false;
}
static bool ExprStmt(std::vector<Statement> block) {
  if (Expr()) {
    if (CurTok.type==SC) {
      printf("%s\n",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      return true;
    }
  }
  if (CurTok.type==SC) {

    printf("%s\n",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return true;
  }
  return false;
}
static bool Stmt(std::vector<Statement> block) {
  if (CurTok.type==LBRA) { //FIRST(Block)
    return Block(block);
  }
  if (CurTok.type==IF) { //FIRST(ifstmt)
    return IfStmt(block);
  }
  if (CurTok.type==WHILE) {
    return WhileStmt(block);
  }
  if (CurTok.type==RETURN) {
    return ReturnStmt(block);
  }
  if ((CurTok.type==SC)||(CurTok.type==IDENT)||(CurTok.type==MINUS)||(CurTok.type==NOT)||(CurTok.type==LPAR)||(CurTok.type==INT_LIT)||(CurTok.type==FLOAT_LIT)||(CurTok.type==BOOL_LIT)) {
    return ExprStmt(block);
  }
  return false;
}
static bool StmtListPrime(std::vector<Statement> block) {
  if (Stmt(block)) {
    return StmtListPrime(block);
  }
  return true;
}
static bool StmtList(std::vector<Statement> block) {
  return StmtListPrime(block);
}
static std::string VarType(); //define for LocalDecl() and Param()
static bool LocalDecl(std::vector<Statement> block) {
  std::string type = VarType();
  if (type!="null") {
    if (CurTok.type==IDENT) {
      std::string name = CurTok.lexeme.c_str();
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (CurTok.type==SC) {
        //make decl and add to block
        std::unique_ptr<Declaration> decl = std::make_unique<Declaration>(type, name);
        block.push_back(*decl);

        printf("%s\n",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        return true;
      }
    }
  }
  return false;
}
static bool LocalDeclsPrime(std::vector<Statement> block) {
  if (LocalDecl(block)) {
    return LocalDeclsPrime(block);
  }
  return true;
}
static bool LocalDecls(std::vector<Statement> block) {
  if (LocalDeclsPrime(block)) {
    return true;
  }
  return false;
}
static bool Block(std::vector<Statement> block) {
  if (CurTok.type==LBRA) {
    printf("%s\n ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (LocalDecls(block)) {
        if (StmtList(block)) {
          if (CurTok.type==RBRA) {
            printf("%s\n ",CurTok.lexeme.c_str());
            CurTok = getNextToken();
            return true;
          }
        }
      }
  }
  return false;
}
static bool Param(std::vector<Declaration> params) {
  std::string type = VarType();
  if (type!="null") {
    if (CurTok.type==IDENT) {
      std::string name = CurTok.lexeme.c_str();
      printf("%s ",CurTok.lexeme.c_str());
      //add this to current args vector for function prototype
      std::unique_ptr<Declaration> param = std::make_unique<Declaration>(type, name);
      params.push_back(*param);
      CurTok = getNextToken();
      return true;
    }
  }
  return false;
}
static bool ParamListPrime(std::vector<Declaration> params) {
  if (CurTok.type==COMMA) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    if (Param(params)) {
      return ParamListPrime(params);
    } 
  }
  return true;
}
static bool ParamList(std::vector<Declaration> params) {
  if (Param(params)) {
    return ParamListPrime(params);
  }
  return false;
}
static bool Params(std::vector<Declaration> params) {
  if (CurTok.type==VOID_TOK) {

    std::string type = "void";
    std::string name = "null";
    std::unique_ptr<Declaration> param = std::make_unique<Declaration>(type, name);
    params.push_back(*param);
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return true; //?
  } else if (ParamList(params)) {
      //printf("%s ",CurTok.lexeme.c_str());
      //CurTok = getNextToken();
      return true;
  }
  return true;
}
static std::string TypeSpec(); //define for FunDecl()
static bool FunDecl(Program* prog) {
  std::string type = TypeSpec();
  if (type!="null") {
    if (CurTok.type==IDENT) {
      std::string name = CurTok.lexeme.c_str();
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (CurTok.type==LPAR) {
        printf("%s ",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        std::vector<Declaration> params;
        if (Params(params)) {
          if (CurTok.type==RPAR) {
            printf("%s ",CurTok.lexeme.c_str());
            CurTok = getNextToken();
            //get block which is a list of statements
            std::vector<Statement> statementBlock;
            if (Block(statementBlock)) {
              //make prototype
              std::unique_ptr<Prototype> proto = std::make_unique<Prototype>(type, name, params);
              //make function class - prototype and body
              std::unique_ptr<BlockClass> body = std::make_unique<BlockClass>(statementBlock);
              std::unique_ptr<Func> fun = std::make_unique<Func>(std::move(proto), std::move(body));
              prog->Statements.push_back(*fun);
              return true;
            }
            //return false;
          }
        }
      }
    }
  }
  return false;
}
static std::string VarType() {
  if (CurTok.type==INT_TOK || CurTok.type==FLOAT_TOK || CurTok.type==BOOL_TOK) {
    printf("%s ",CurTok.lexeme.c_str());
    std::string type = CurTok.lexeme.c_str();
    CurTok = getNextToken();
    return type;
  }
  return "null";
}
static std::string TypeSpec() {
  if (CurTok.type==VOID_TOK) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    return "void";
  }
  return VarType();
}
static bool VarDecl(Program* prog) {
  std::string type = VarType();
  if (type!="null") {
    if (CurTok.type==IDENT) {
      std::string name = CurTok.lexeme.c_str();
      printf("%s ",CurTok.lexeme.c_str());
      CurTok = getNextToken();
      if (CurTok.type==SC) {

        std::unique_ptr<Declaration> decl = std::make_unique<Declaration>(type, name);
        prog->Statements.push_back(*decl);

        printf("%s\n",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        return true;
      }
    }
  }
  return false;
}
static bool Decl(Program* prog) {
  if (CurTok.type==VOID_TOK) {
    return FunDecl(prog);
  }
  TOKEN CurTokCopy = CurTok;
  TOKEN lookahead = getNextToken();
  TOKEN lookahead2 = getNextToken();
  if (lookahead2.type==LPAR) {
    putBackToken(lookahead2);
    putBackToken(lookahead);
    putBackToken(CurTokCopy);
    CurTok = getNextToken();
    return FunDecl(prog);
  }
  putBackToken(lookahead2);
  putBackToken(lookahead);
  putBackToken(CurTokCopy);
  return (VarDecl(prog));
}
static bool DeclListPrime(Program* prog) {
  if (Decl(prog)) {
    return DeclListPrime(prog);
  }
  return true; 
}
static bool DeclList(Program* prog) {
  if (Decl(prog)) {
    return DeclListPrime(prog);
  }
  return false;
}
static bool Extern(Program* prog) {
  if (CurTok.type==EXTERN) {
    printf("%s ",CurTok.lexeme.c_str());
    CurTok = getNextToken();
    std::string type = TypeSpec();
    if (type!="null") {
      if (CurTok.type==IDENT) {
        std::string name = CurTok.lexeme.c_str();
        printf("%s ",CurTok.lexeme.c_str());
        CurTok = getNextToken();
        if (CurTok.type==LPAR) {
          printf("%s ",CurTok.lexeme.c_str());
          CurTok = getNextToken();
          //if params returns a string store it. its allowed to be empty
          std::vector<Declaration> params;
          if (Params(params)) {
            if (CurTok.type==RPAR) {
              printf("%s ",CurTok.lexeme.c_str());
              CurTok = getNextToken();
              if (CurTok.type==SC) {
                //make prototype class type name args
                //Prototype proto = new Prototype(type, name, params);
                std::unique_ptr<Prototype> proto = std::make_unique<Prototype>(type, name, params); //maybe auto
                //add prototype class to ast/return prototype
                prog->Statements.push_back(*proto);
                printf("%s\n",CurTok.lexeme.c_str());
                CurTok = getNextToken();
                return true;
              }
            }
          }
        }
      }
    }
  }
  return false;
}
static bool ExternListPrime(Program* prog) {
  if (Extern(prog)) {
    return ExternListPrime(prog);
  }
  return false;
}
static bool ExternList(Program* prog) {
  if (Extern(prog)) {
    return ExternListPrime(prog);
  }
  return false;
}
//entry point
static void parser() { //std::unique_ptr<Program>
  //ast is made up of its nodes
  //std::unique_ptr<Program> TODELETE = std::make_unique<Program>();
  Program prog;

  CurTok = getNextToken();
  if (ExternList(&prog)) {
    if (DeclList(&prog)) {
      if (CurTok.type==EOF_TOK) {
        printf("Success\n"); 
      }
    }
  }
  if (DeclList(&prog)) {
    if (CurTok.type==EOF_TOK) {
      printf("Success\n");
    }
  }
  printf("Fail\n");
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

//inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
//                                     const AST &ast) {
//  os << ast.to_string();
//  return os;
//}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv) {
  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  //getNextToken();
  //while (CurTok.type != EOF_TOK) {
    //fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
            //CurTok.type);
    //getNextToken();
  //}
  //fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  parser(); // auto tree = parser();
  fprintf(stderr, "Parsing Finished\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
