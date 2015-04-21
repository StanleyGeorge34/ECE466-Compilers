/*
	Stanley George
	ECE466:Compilers
	Professor Jeff Hakner
	Assignment 3: Declaration Parsing and Building Internal Represenations
*/
%{
	#include <stdio.h>
	#include <string.h>
	#include <stdlib.h>
	#include "yysymtab.h"
	scopeList *SCOPE_STACK;
	scope *GLOBAL_SCOPE;
	extern int lineno;
	extern char *filename;
	void yyerror(const char *s);
	void assign(char *s, int operatorTokenValue, long long itokval, symtab *table);

	int isBlockScope = 0;
	int isStructScope = 0;
	int hideStructdef = 0;
%}

%error-verbose

%token  CHARLIT TOKEOF ELLIPSIS AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE
%token	ENUM EXTERN FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN SHORT SIGNED STATIC STRUCT SWITCH
%token	TYPEDEF UNION UNSIGNED VOID VOLATILE WHILE _BOOL _COMPLEX _IMAGINARY

%token ',' '=' PLUSEQ MINUSEQ TIMESEQ DIVEQ ANDEQ OREQ MODEQ SHREQ SHLEQ XOREQ
%token LOGOR LOGAND '|' '^' '&' EQEQ NOTEQ '<' LTEQ '>' GTEQ SHL SHR '-' '+' '*' '/' '%'
%token '!' '~' PLUSPLUS MINUSMINUS UNARY_PLUS UNARY_MINUS PTR_DREF ADDRESS_OF CAST SIZEOF
%token '(' ')' '[' ']' INDSEL '.'

%code requires {
  #include "AST.h"
	#include "yysymtab.h"
}

%union {
  struct identifier {
      char *tok;
      symrec *symbol;
  } ID;
   struct keyword {
      char *tok;
      int tokval;
  } KW;
  struct operator_ {
      char *tok;
      int tokval;
  } OP;
  struct number {
      char *itok;
      char *itype;
      char *rtok;
      char *rtype;
      long long itokval;
      long double rtokval;
      char *num_type;
  } N;
  struct string {
      unsigned char *tokval;
      int length;
  } S;
	struct astnode_builder {
		astnode *Head;
		astnode *Tail;
		storage_class_code storage_class;
	} astnode_builder;
}

%token <ID> IDENT
%token <N>  NUMBER
%token <S>  STRING
%type <astnode_builder> expression cast_expression primary_expression postfix_expression conditional_expression
	assignment_expression unary_expression additive_expression constant_expression AND_expression logical_OR_expression
	inclusive_OR_expression exclusive_OR_expression logical_AND_expression equality_expression relational_expression
	shift_expression multiplicative_expression statement expression_statement iteration_statement
%type <astnode_builder> type_specifier declaration declaration_list declaration_specifiers pointer abstract_declarator
  declarator direct_declarator direct_abstract_declarator init_declarator init_declarator_list function_definition
  storage_class_specifier struct_or_union struct_or_union_specifier struct_declarator specifier_qualifier_list
  struct_declaration struct_declaration_list struct_declarator_list parameter_list parameter_type_list 
  parameter_declaration 
%type <OP.tokval> unary_operator assignment_operator

%start translation_unit

%%
translation_unit:
	external_declaration
	|translation_unit external_declaration
	;
external_declaration:
	function_definition
	|declaration
	;
function_definition:
	declaration_specifiers declarator declaration_list 
		{ push_new_scope(SCOPE_STACK); SCOPE_STACK->end->scopeType = _FUNCTION; } compound_statement 
		{
			printf("Defined function1\n");
		}
	|declaration_specifiers declarator 
		{ 
			push_new_scope(SCOPE_STACK); SCOPE_STACK->end->scopeType = _FUNCTION; 
			if ($2.Head != NULL && $2.Tail != NULL) {
				$2.Head->fcn_node.file = strdup(filename);
				$2.Head->fcn_node.line = lineno;
				if ($2.Head->fcn_node.arguments != NULL) {
					astnode *cur_arg = $2.Head->fcn_node.arguments;
					while (cur_arg != NULL) {
						checkInstallation(cur_arg->fcn_arg_node.arg_sym, SCOPE_STACK->end, _DEFAULT);
						cur_arg = cur_arg->fcn_arg_node.next_arg;
					}
				}
			}
		} 
		compound_statement 
		{
			if ($2.Head != NULL && $2.Tail != NULL) {
				int scopeCode = SCOPE_STACK->end->scopeType;
				int scopeLine = SCOPE_STACK->end->line;
				int astType2 = get_astnode_type($2.Tail);
				switch(astType2) {
					case AST_PTR:
						$2.Tail->ptr_node.baseType = $1.Head;
						break;
					case AST_FCN:
						$2.Tail->fcn_node.returnType = $1.Head;
						break;
				}
				if ($1.storage_class != _EXTERN && $1.storage_class != _STATIC) {
					if ($1.storage_class == _AUTOMATIC) ;	
					else {		
						fprintf(stderr, "Warning:%s:%d:Invalid storage class in scope starting @ line %d", 
							filename, lineno, scopeLine);
						fprintf(stderr, "...using default [stg_class = extern]\n");
					}
					$2.Head->fcn_node.storageType = _EXTERN;
				}
				else {
					$2.Head->fcn_node.storageType = $1.storage_class;
				}
				$2.Head->fcn_node.isDefined = 1;
				$$.Head = $2.Head;
				$$.Tail = $1.Head;
				symtab *symbol_table = getSymbolTable($$.Head->fcn_node.fcn_sym, SCOPE_STACK->end, _DEFAULT);
				symrec *symbol = lookup($$.Head->fcn_node.fcn_sym, symbol_table, _DEFAULT);
				char *scopeType;
				switch (scopeCode) {
					case _FILE:
						scopeType = "FILE";
						break;
					case _FUNCTION:
						scopeType = "FUNCTION";
						break;
					case _BLOCK:
						scopeType = "BLOCK";
						break;
					case _PROTOTYPE:
						scopeType = "PROTOTYPE";
						break;
				}
				symbol->ast_node = $$.Head;
				// printf("%s defined in %s:%d [in %s scope starting @ %s:%d] w/ AST representation:\n", 
				// 	symbol->symtok, symbol->file, symbol->line, scopeType, symbol->file, scopeLine);
				// astnode_print(symbol->ast_node, 0);
				// printf("=========================================================================================\n");
			}
			else {
				$$.Head = $$.Tail = NULL;
			}
		}
	;
declaration:
	declaration_specifiers init_declarator_list ';' 
		{
			if ($2.Head != NULL && $2.Tail != NULL) {
				int scopeCode = SCOPE_STACK->end->scopeType;
				int scopeLine = SCOPE_STACK->end->line;
				char *scopeType;
				int isIncompleteStructType = 0;
				if (get_astnode_type($1.Head) == AST_STRUCT)
					if ($1.Head->su_node.isComplete == 0) {
						isIncompleteStructType = 1;
					}
				int astType2 = get_astnode_type($2.Tail);
				switch (astType2) {
					case AST_VAR:
						if (isIncompleteStructType == 1) {
							fprintf(stderr, "Error:%s:%d:%s refers to incomplete struct/union definition\n",
								filename, lineno, $2.Tail->var_node.var_sym);
							goto error;
						}
						else 
							$2.Head->var_node.varType = $1.Head;
						break;
					case AST_PTR:
						$2.Tail->ptr_node.baseType = $1.Head;
						break;
					case AST_ARR:
						if (isIncompleteStructType == 1) {
							fprintf(stderr, "Error:%s:%d:%s is array of incomplete struct/union\n",
								filename, lineno, $2.Tail->var_node.var_sym);
							goto error;
						}
						else {
							$2.Tail->arr_node.etype = $1.Head;
							$2.Head->var_node.storageType = $1.storage_class;
							$$.storage_class = $1.storage_class;
						}
						break;
					case AST_FCN:
						$2.Tail->fcn_node.returnType = $1.Head;
						break;
				}
				switch (get_astnode_type($2.Head)) {
					case AST_FCN:
						//In file scope we only allow STATIC and EXTERN storage classes
						//If not in file scope, we only allow EXTERN storage class
						if (scopeCode != _FILE) {
							if ($1.storage_class != _EXTERN) {
								if ($1.storage_class == _AUTOMATIC);
								else {
									fprintf(stderr, "Warning:%s:%d:Invalid storage class in scope starting @ line %d", 
										filename, lineno, scopeLine);
									fprintf(stderr, "...using default [stg_class = extern]\n");
									
								}
								$2.Head->fcn_node.storageType = _EXTERN;
								$$.storage_class = _EXTERN;
							}
							else {
								$2.Head->fcn_node.storageType = $1.storage_class;
								$$.storage_class = $1.storage_class;
							}
						}
						else {
							if ($1.storage_class != _EXTERN && $1.storage_class != _STATIC) {
								if ($1.storage_class == _AUTOMATIC);
								else {
									fprintf(stderr, "Warning:%s:%d:Invalid storage class in scope starting @ line %d", 
										filename, lineno, scopeLine);
									fprintf(stderr, "...using default [stg_class = extern]\n");
								}
								$2.Head->fcn_node.storageType = _EXTERN;
								$$.storage_class = _EXTERN;
							}
							else {
								$2.Head->fcn_node.storageType = $1.storage_class;
								$$.storage_class = $1.storage_class;
							}
						}
						break;
					case AST_VAR:
						$2.Head->var_node.storageType = $1.storage_class;
						if (scopeCode != _FILE)
							$$.storage_class = $1.storage_class;
						else {
							int storage_class = $1.storage_class;
							if (storage_class != _EXTERN && storage_class != _STATIC) {
								if (storage_class == _AUTOMATIC) ; //don't complain bc WE initialized it to AUTOMATIC
								else {
									fprintf(stderr, "Warning:%s:%d:Invalid storage class in scope starting @ line %d", 
										filename, lineno, scopeLine);
									fprintf(stderr, "...using default [stg_class = extern]\n");
								}
								$2.Head->var_node.storageType = _EXTERN;
								$$.storage_class = _EXTERN;
							}
						}
						break;
				}
				$$.Head = $2.Head;
				$$.Tail = $1.Head;
				int astType1 = get_astnode_type($2.Head);
				symtab *symbol_table;
				symrec *symbol;
				switch (astType1) {
					case AST_FCN:
						symbol_table = getSymbolTable($$.Head->fcn_node.fcn_sym, SCOPE_STACK->end, _DEFAULT);
						symbol = lookup($$.Head->fcn_node.fcn_sym, symbol_table, _DEFAULT);
						break;
					case AST_VAR:
						symbol_table = getSymbolTable($$.Head->var_node.var_sym, SCOPE_STACK->end, _DEFAULT);
						symbol = lookup($$.Head->var_node.var_sym, symbol_table, _DEFAULT);
						break;
				}
				switch (scopeCode) {
					case _FILE:
						scopeType = "FILE";
						break;
					case _FUNCTION:
						scopeType = "FUNCTION";
						break;
					case _BLOCK:
						scopeType = "BLOCK";
						break;
					case _PROTOTYPE:
						scopeType = "PROTOTYPE";
						break;
				}
				symbol->ast_node = $$.Head;
				// printf("%s defined in %s:%d in %s scope starting @ %s:%d w/ AST representation:\n", 
				// 	symbol->symtok, symbol->file, symbol->line, scopeType, symbol->file, scopeLine);
				// astnode_print(symbol->ast_node, 0);
				// printf("-----------------------------------------------------------------------------------------\n");
			}
			else {
				$$.Head = $$.Tail = NULL;
			}
			error:
				$$.Head = $$.Tail = NULL;
		}
	|declaration_specifiers ';' 
		{
			if ($1.Head != NULL) {
				if (get_astnode_type($1.Head) == AST_STRUCT) {
					scope *root_scope = SCOPE_STACK->end;
					while (root_scope->scopeType == _STRUCT_UNION)
						root_scope = root_scope->prevScope;
					symrec *tag_id = lookup($1.Head->su_node.tag, root_scope->table, _TAG);
					if (hideStructdef == 1) {
						tag_id = install($1.Head->su_node.tag, root_scope->table, _TAG, NULL);
						tag_id->ast_node = ast_newnode(AST_STRUCT);
						tag_id->ast_node->su_node.tag = strdup($1.Head->su_node.tag);
						tag_id->ast_node->su_node.isComplete = 0;
						hideStructdef = 0;
					}
					else
						tag_id->ast_node = $1.Head;
					$$.Head = $$.Tail = tag_id->ast_node;
				}
			}
		}
	;

declaration_list:
	declaration
	|declaration_list declaration
	;
declaration_specifiers:
	storage_class_specifier declaration_specifiers 
		{
			$$.Head = $2.Head;
			$$.Tail = $2.Tail;
			$$.storage_class = $1.storage_class;
		}
	|storage_class_specifier 
		{
			$$.storage_class = $1.storage_class;
			$$.Head = $1.Head;
			$$.Tail = $1.Tail;
		}
	|type_specifier declaration_specifiers
		{
			$1.Tail->scalar_node.modifies = $2.Head;
			$$.Head = $1.Head;
			$$.Tail = $2.Tail;
			$$.storage_class = $2.storage_class;
		}
	|type_specifier 
		{ 
			$$.Head = $1.Head;
			$$.Tail = $1.Tail;
			$$.storage_class = _AUTOMATIC;
		}
	|type_qualifier declaration_specifiers {}
	|type_qualifier {}
	;
storage_class_specifier:
	AUTO 				{$$.storage_class = _AUTOMATIC;}
	|REGISTER 	{$$.storage_class = _REGISTER;}
	|STATIC 		{$$.storage_class = _STATIC;}
	|EXTERN 		{$$.storage_class = _EXTERN;}
	|TYPEDEF 		{$$.storage_class = _TYPEDEF;}
	;
type_specifier:
	VOID
		{
    	astnode *void_scalar = ast_newnode(AST_SCALAR);
     	void_scalar->scalar_node.scalar_type = _VOID;
     	$$.Head = $$.Tail = void_scalar;
    }
	|CHAR
		{
			astnode *char_scalar = ast_newnode(AST_SCALAR);
     	char_scalar->scalar_node.scalar_type = _CHAR;
     	$$.Head = $$.Tail = char_scalar;
		}
	|SHORT
		{
			astnode *short_scalar = ast_newnode(AST_SCALAR);
     	short_scalar->scalar_node.scalar_type = _SHORT;
     	$$.Head = $$.Tail = short_scalar;
		}
	|INT
    {
     	astnode *integer_scalar = ast_newnode(AST_SCALAR);
     	integer_scalar->scalar_node.scalar_type = _INT;
     	$$.Head = $$.Tail = integer_scalar;
    }
	|LONG
    {
    	astnode *long_scalar = ast_newnode(AST_SCALAR);
     	long_scalar->scalar_node.scalar_type = _LONG;
     	$$.Head = $$.Tail = long_scalar;
    }
	|FLOAT
    {
     	astnode *float_scalar = ast_newnode(AST_SCALAR);
     	float_scalar->scalar_node.scalar_type = _FLOAT;
     	$$.Head = $$.Tail = float_scalar; 
    }
	|DOUBLE
    {
      astnode *double_scalar = ast_newnode(AST_SCALAR);
     	double_scalar->scalar_node.scalar_type = _DOUBLE;
     	$$.Head = $$.Tail = double_scalar;
    }
	|SIGNED
    {
      astnode *signed_scalar = ast_newnode(AST_SCALAR);
     	signed_scalar->scalar_node.scalar_type = _SIGNED;
     	$$.Head = $$.Tail = signed_scalar;
    }
	|UNSIGNED
    {
      astnode *unsigned_scalar = ast_newnode(AST_SCALAR);
     	unsigned_scalar->scalar_node.scalar_type = _UNSIGNED;
     	$$.Head = $$.Tail = unsigned_scalar;
    }
	|_BOOL
    {
      astnode *bool_scalar = ast_newnode(AST_SCALAR);
     	bool_scalar->scalar_node.scalar_type = BOOL;
     	$$.Head = $$.Tail = bool_scalar;
    }
	|_COMPLEX
    {
      astnode *complex_scalar = ast_newnode(AST_SCALAR);
     	complex_scalar->scalar_node.scalar_type = COMPLEX;
     	$$.Head = $$.Tail = complex_scalar;
    }
	|struct_or_union_specifier {
			$$.Head = $$.Tail = $1.Head;
		}
	|enum_specifier {}
//|typedef_name {}
	;
type_qualifier:
	CONST
	|VOLATILE
	|RESTRICT
	;
struct_or_union_specifier:
	struct_or_union IDENT 
		{
			scope *root_scope = SCOPE_STACK->end;
			while (root_scope->scopeType == _STRUCT_UNION)
				root_scope = root_scope->prevScope;
			symrec *symbol = lookup($2.tok, root_scope->table, _TAG);
			//if tag is new, then install into sym tab 
			if (symbol == NULL) {
				symbol = install($2.tok, root_scope->table, _TAG, NULL);
				$1.Head->su_node.tag = strdup($2.tok);
				symbol->ast_node = $1.Head;
			}
			else
				$1.Head = symbol->ast_node;
			$1.Head->su_node.file = strdup(filename);
			$1.Head->su_node.line = lineno;
			isStructScope = 1;
		} 
		'{' { push_new_scope(SCOPE_STACK); SCOPE_STACK->end->scopeType = _STRUCT_UNION;} 
			struct_declaration_list
		'}' 
			{
				$1.Head->su_node.symbolTable = SCOPE_STACK->end->table;
				pop_curr_scope(SCOPE_STACK); //will cause seg fault if we try to free memory of scope just popped...
				$1.Head->su_node.isComplete = 1;
				scope *root_scope = SCOPE_STACK->end;
				if (root_scope->scopeType != _STRUCT_UNION)
					isStructScope = 0;
				while (root_scope->scopeType == _STRUCT_UNION)
					root_scope = root_scope->prevScope;
				symtab *symbol_table = getSymbolTable($2.tok, root_scope, _TAG);
				symrec *symbol = lookup($2.tok, symbol_table, _TAG);
				symbol->ast_node = $1.Head;
				$$.Head = $$.Tail = $1.Head;
				int scopeCode = root_scope->scopeType;
				int scopeLine = root_scope->line;
				char *scopeType;
				switch (scopeCode) {
					case _FILE:
						scopeType = "FILE";
						break;
					case _FUNCTION:
						scopeType = "FUNCTION";
						break;
					case _BLOCK:
						scopeType = "BLOCK";
						break;
					case _PROTOTYPE:
						scopeType = "PROTOTYPE";
						break;
				}
				// printf("%s defined in %s:%d in %s scope starting @ %s:%d w/ AST representation:\n", 
				// 	symbol->symtok, symbol->file, symbol->line, scopeType, symbol->file, scopeLine);
				// astnode_print($$.Head, 0);
				// printf("-----------------------------------------------------------------------------------------\n");
			} 
	|struct_or_union '{' struct_declaration_list '}' {}
	|struct_or_union IDENT 
		{ //back track to nearest enclosing scope
			scope *root_scope = SCOPE_STACK->end;
			while (root_scope->scopeType == _STRUCT_UNION)
				root_scope = root_scope->prevScope;
			//look up previoius installation of tag
			symtab *tag_symtab = getSymbolTable($2.tok, root_scope, _TAG);
			symrec *tag_sym;
			if (tag_symtab != NULL) {
				tag_sym = lookup($2.tok, tag_symtab, _TAG);
				$$.Head = $$.Tail = tag_sym->ast_node; //pass up ast node of found struct tag
				hideStructdef = 1;
			}
			else {
				tag_sym = install($2.tok, root_scope->table, _TAG, NULL); //install tag into symtab
				$1.Head->su_node.tag = strdup($2.tok);
				tag_sym->ast_node = $$.Head = $$.Tail = $1.Head;
			}
		}
	;
struct_or_union:
	STRUCT 
		{ //create new incomplete struct ast node and pass it up the stack
			astnode *struct_node = ast_newnode(AST_STRUCT);
			struct_node->su_node.isComplete = 0;
			$$.Head = $$.Tail = struct_node;
		}
	|UNION {}
	;
struct_declaration_list:
	struct_declaration {}
	|struct_declaration_list struct_declaration {}
	;
init_declarator_list:
	init_declarator {$$.Head = $1.Head; $$.Tail = $1.Tail;}
	|init_declarator_list ',' init_declarator {$$.Head = $1.Head; $$.Tail = $1.Tail;}
	;
init_declarator:
	declarator {$$.Head = $1.Head; $$.Tail = $1.Tail;}
	|declarator '=' initializer
	;
struct_declaration:
	specifier_qualifier_list struct_declarator_list ';' 
		{
			if ($2.Head != NULL && $2.Tail != NULL) {
				int isIncompleteStructType = 0;
				if (get_astnode_type($1.Head) == AST_STRUCT)
					if ($1.Head->su_node.isComplete == 0)
						isIncompleteStructType = 1;
				int astType2 = get_astnode_type($2.Tail);
				switch (astType2) {
					case AST_PTR:
						$2.Tail->ptr_node.baseType = $1.Head;
						break;
					case AST_ARR:
						if (isIncompleteStructType == 1) {
							fprintf(stderr, "Error:%s:%d:%s is array of incomplete struct/union\n",
								filename, lineno, $2.Head->su_member_node.memtok);
							$$.Head = $$.Tail = NULL;
						} 
						else
							$2.Tail->arr_node.etype = $1.Head;
						break;
					case AST_FCN:
						$2.Tail->fcn_node.returnType = $1.Head;
						break;
					case AST_SU_MEMBER:
						if (isIncompleteStructType == 1) {
							fprintf(stderr, "Error:%s:%d:%s refers to incomplete struct/union definition\n",
								filename, lineno, $2.Head->su_member_node.memtok);
							$$.Head = $$.Tail = NULL;
						} 
						else
							$2.Tail->su_member_node.memberType = $1.Head;
						break;
				}
				symrec *symbol = lookup($2.Head->su_member_node.memtok, SCOPE_STACK->end->table, _SU_MEMBER);
				symbol->ast_node = $2.Head;
				if (isIncompleteStructType == 0 || astType2 == AST_PTR || astType2 == AST_FCN) {
					$$.Head = $2.Head;
					$$.Tail = $1.Head;
				}
			} else $$.Head = $$.Tail = NULL;
		}
	;
specifier_qualifier_list:
	type_specifier specifier_qualifier_list {}
		{
			$1.Tail->scalar_node.modifies = $2.Head;
			$$.Head = $1.Head;
			$$.Tail = $2.Head;
		}
	|type_specifier {$$.Head = $1.Head; $$.Tail = $1.Tail; }
	|type_qualifier specifier_qualifier_list {}
	|type_qualifier {}
	;
struct_declarator_list:
	struct_declarator {$$.Head = $1.Head; $$.Tail = $1.Tail;}
	|struct_declarator_list ',' struct_declarator {  }
	;
struct_declarator:
	declarator 
		{$$.Head = $1.Head; $$.Tail = $1.Tail;}
	|declarator ':' constant_expression {}
	|':' constant_expression {}
	;
enum_specifier:
	ENUM IDENT '{' enumerator_list '}'
	|ENUM '{' enumerator_list '}'
	|ENUM IDENT '{' enumerator_list ',' '}'
	|ENUM '{' enumerator_list ',' '}'
	|ENUM IDENT
	;
enumerator_list:
	enumerator
	|enumerator_list ',' enumerator
	;
enumeration_constant:
	IDENT
	;
enumerator:
	enumeration_constant
	|enumeration_constant '=' constant_expression
	;
declarator:
		pointer direct_declarator
		{
			if ($2.Head != NULL && $2.Tail != NULL) {
				int astType2 = get_astnode_type($2.Tail);
				switch (astType2) {
					case AST_VAR:
						$2.Head->var_node.varType = $1.Head;
						break;
					case AST_ARR:
						$2.Tail->arr_node.etype = $1.Head;
						break;
					case AST_PTR:
						$2.Tail->ptr_node.baseType = $1.Head;
						break;
					case AST_FCN:
						$2.Tail->fcn_node.returnType = $1.Head;
						break;
					case AST_SU_MEMBER:
						$2.Tail->su_member_node.memberType = $1.Head;
						break;
				}
				$$.Head = $2.Head;
				$$.Tail = $1.Tail;
			}
			else {
				$$.Head = $$.Tail = NULL;
			}
		}
	|direct_declarator { $$.Head = $1.Head; $$.Tail = $1.Tail;}
	;
direct_declarator:
	IDENT
    {    
     	symrec *symbol;
			if (isStructScope == 0) {
  			symbol = checkInstallation($1.tok, SCOPE_STACK->end, _DEFAULT);
  			if (symbol != NULL) {
  				astnode *var = ast_newnode(AST_VAR);
					var->var_node.var_sym = strdup($1.tok);
					var->var_node.file = strdup(filename);
					var->var_node.line = lineno;
					$$.Head = $$.Tail = var;
				}
				else 
				$$.Head = $$.Tail = NULL;
			}
			else {
				symbol = checkInstallation($1.tok, SCOPE_STACK->end, _SU_MEMBER);
				if (symbol != NULL) {
  				astnode *struct_memb = ast_newnode(AST_SU_MEMBER);
					struct_memb->su_member_node.memtok = strdup($1.tok);
					struct_memb->su_member_node.file = strdup(filename);
					struct_memb->su_member_node.line = lineno;
					$$.Head = $$.Tail = struct_memb;
					hideStructdef = 0;
				}
				else 
				$$.Head = $$.Tail = NULL;
			}
    }
	|'(' declarator ')' 
		{ 
			if ($2.Head != NULL && $2.Tail != NULL) {
				$$.Head = $2.Head; 
				$$.Tail = $2.Tail;
			} 
			else {
				$$.Head = $$.Tail = NULL;
			} 
		}
	|direct_declarator '[' ']'
    {
     if ($1.Head != NULL && $1.Tail != NULL) {
				int astType = get_astnode_type($1.Tail);
				int numVal = -1;
				astnode *array_node = ast_newnode(AST_ARR);
				array_node->arr_node.num_elements = numVal;
				switch (astType) {
					case AST_VAR:
						array_node->arr_node.etype = $1.Tail->var_node.varType;
						$1.Tail->var_node.varType = array_node;
						$$.Tail = $1.Tail->var_node.varType;
						break;
					case AST_ARR:
						array_node->arr_node.etype = $1.Tail->arr_node.etype;
						$1.Tail->arr_node.etype = array_node;
						$$.Tail = $1.Tail->arr_node.etype;
						break;
					case AST_PTR:
						array_node->arr_node.etype = $1.Tail->ptr_node.baseType;
						$1.Tail->ptr_node.baseType = array_node;
						$$.Tail = $1.Tail->ptr_node.baseType;
						break;
					case AST_SU_MEMBER:
						array_node->arr_node.etype = $1.Tail->su_member_node.memberType;
						$1.Tail->su_member_node.memberType = array_node;
						$$.Tail = $1.Tail->su_member_node.memberType;
						break;
				}
				$$.Head = $1.Head;
			}
			else {
				$$.Head = $$.Tail = NULL;
			} 
    }
	|direct_declarator '[' type_qualifier_list ']' {}
  |direct_declarator '[' type_qualifier_list assignment_expression ']' {}
	|direct_declarator '[' assignment_expression ']' 
		{
			if ($1.Head != NULL && $1.Tail != NULL) {
				int astType = get_astnode_type($1.Tail);
				int numType = $3.Head->num_node.num_type;
				int numVal;
				switch (numType) {
					case _U:
						numVal = $3.Head->num_node.val.u;
					case _L:
						numVal = $3.Head->num_node.val.l;
						break;
					case _UL:
						numVal = $3.Head->num_node.val.ul;
						break;
					case _ULL:
						numVal = $3.Head->num_node.val.ull;
						break;
					case _LL:
						numVal = $3.Head->num_node.val.ll;
						break;
					case _I:
						numVal = $3.Head->num_node.val.i;
						break;
				}
				astnode *array_node = ast_newnode(AST_ARR);
				array_node->arr_node.num_elements = numVal;
				switch (astType) {
					case AST_VAR:
							array_node->arr_node.etype = $1.Tail->var_node.varType;
							$1.Tail->var_node.varType = array_node;
							$$.Tail = $1.Tail->var_node.varType;
						break;
					case AST_ARR:
						array_node->arr_node.etype = $1.Tail->arr_node.etype;
						$1.Tail->arr_node.etype = array_node;
						$$.Tail = $1.Tail->arr_node.etype;
						break;
					case AST_PTR:
						array_node->arr_node.etype = $1.Tail->ptr_node.baseType;
						$1.Tail->ptr_node.baseType = array_node;
						$$.Tail = $1.Tail->ptr_node.baseType;
						break;
					case AST_SU_MEMBER:
						array_node->arr_node.etype = $1.Tail->su_member_node.memberType;
						$1.Tail->su_member_node.memberType = array_node;
						$$.Tail = $1.Tail->su_member_node.memberType;
						break;
				}
				$$.Head = $1.Head;
			}
			else {
				$$.Head = $$.Tail = NULL;
			}
		}
	|direct_declarator '[' STATIC type_qualifier_list assignment_expression ']' {}
	|direct_declarator '[' STATIC assignment_expression ']' {}
	|direct_declarator '[' type_qualifier_list STATIC assignment_expression ']' {}
	|direct_declarator '[' type_qualifier_list '*' ']' {}
	|direct_declarator '[' '*' ']' {}
	|direct_declarator '(' 
		{  /*
				if tail is ptr then we want to make ptr to fcn
				if tail is arr then we want to complain bc cant have arr of fcns
				if tail is var then we want to make fcn
				*/
			if ($1.Head != NULL && $1.Tail != NULL) {
				if (get_astnode_type($1.Tail) == AST_VAR) {
						push_new_scope(SCOPE_STACK);
						SCOPE_STACK->end->scopeType = _PROTOTYPE;
				}
			}
		} 
		parameter_type_list ')' 
		{
			if ($1.Head != NULL && $1.Tail != NULL) {
				astnode *function;
				switch (get_astnode_type ($1.Tail)) {
					case AST_VAR:
						function = ast_newnode(AST_FCN);
						function->fcn_node.fcn_sym = strdup($1.Head->var_node.var_sym);
						function->fcn_node.storageType = _EXTERN;
						function->fcn_node.isDefined = 0;
						function->fcn_node.arguments = $4.Head;
						$$.Head = $$.Tail = function;
						pop_curr_scope(SCOPE_STACK);
						break;
					case AST_ARR:
						fprintf(stderr, "Error:%s:%d:Invalid declaration array of functions\n",filename, lineno);
						$$.Head = $$.Tail = NULL;
						break;
					case AST_PTR:
						function = ast_newnode(AST_FCN);
						function->fcn_node.storageType = _EXTERN;
						function->fcn_node.returnType = $1.Head->var_node.varType;
						function->fcn_node.arguments = $4.Head;
						$$.Head = $$.Tail = function;
						$1.Tail->ptr_node.baseType = function;
						$$.Head = $1.Head;
						$$.Tail = function;
						break;
				}
			} 
			else {
				$$.Head = $$.Tail = NULL;
			}

		}
	|direct_declarator '(' identifier_list ')' { }
	|direct_declarator '(' 
		{  /*
				if tail is ptr then we want to make ptr to fcn
				if tail is arr then we want to complain bc cant have arr of fcns
				if tail is var then we want to make fcn
				*/
			if ($1.Head != NULL && $1.Tail != NULL) {
				if (get_astnode_type($1.Tail) == AST_VAR) {
						push_new_scope(SCOPE_STACK); 
						SCOPE_STACK->end->scopeType = _PROTOTYPE;
				}
			}
		} 
		')' 
		{ 
			if ($1.Head != NULL && $1.Tail != NULL) {
				astnode *function;
				switch (get_astnode_type ($1.Tail)) {
					case AST_VAR:
						function = ast_newnode(AST_FCN);
						function->fcn_node.fcn_sym = strdup($1.Head->var_node.var_sym);
						function->fcn_node.storageType = _EXTERN;
						function->fcn_node.isDefined = 0;
						$$.Head = $$.Tail = function;
						pop_curr_scope(SCOPE_STACK);
						break;
					case AST_ARR:
						fprintf(stderr, "Error:%s:%d:Invalid declaration array of functions\n",filename, lineno);
						$$.Head = $$.Tail = NULL;
						break;
					case AST_PTR:
						function = ast_newnode(AST_FCN);
						function->fcn_node.storageType = _EXTERN;
						function->fcn_node.returnType = $1.Head->var_node.varType;
						$$.Head = $$.Tail = function;
						$1.Tail->ptr_node.baseType = function;
						$$.Head = $1.Head;
						$$.Tail = function;
						break;
				}
			} 
			else {
				$$.Head = $$.Tail = NULL;
			}
		}
	;
pointer:
	'*' type_qualifier_list {}
	|'*' { $$.Head = $$.Tail = ast_newnode(AST_PTR);}
	|'*' type_qualifier_list pointer {}
	|'*' pointer 
		{ 
			$$.Head = ast_newnode(AST_PTR);
			$$.Head->ptr_node.baseType = $2.Head;
			$$.Tail = $2.Tail;
		}
	;
type_qualifier_list:
	type_qualifier
	|type_qualifier_list type_qualifier
	;
parameter_type_list:
	parameter_list {$$.Head = $$.Tail = $1.Head;}
	|parameter_list ',' ELLIPSIS {}
	;
parameter_list:
	parameter_declaration 
		{
			if ($1.Head != NULL && $1.Tail != NULL)
				$$.Head = $$.Tail = $1.Head;
			else
				$$.Head = $$.Tail = NULL;
		}
	|parameter_list ',' parameter_declaration 
		{
			if ($1.Tail != NULL && $3.Head != NULL) {
				$$.Head = $1.Head;
				$1.Tail->fcn_arg_node.next_arg = $3.Head;
				$3.Head->fcn_arg_node.next_arg = NULL;
				$$.Tail = $3.Head;
			}
			else 
				$$.Head = $$.Tail = NULL;
		}
	;
parameter_declaration:
	declaration_specifiers declarator 
		{ 
			if ($2.Head != NULL && $2.Tail != NULL) {
				if (get_astnode_type($2.Head) == AST_FCN) {
					fprintf(stderr, "Error:%s:%d:Arguments to functions cannot be other functions\n", filename, lineno);
				}
				else {
					switch (get_astnode_type($2.Tail)) {
						case AST_VAR:
							$2.Head->var_node.varType = $1.Head;
							break;
						case AST_PTR:
							$2.Tail->ptr_node.baseType = $1.Head;
							break;
						case AST_ARR:
							$2.Tail->arr_node.etype = $1.Head;
							$2.Head->var_node.storageType = $1.storage_class;
							$$.storage_class = $1.storage_class;
							break;
						case AST_FCN:
						$2.Tail->fcn_node.returnType = $1.Head;
						break;
					}
					astnode *fcn_arg = ast_newnode(AST_ARG);
					fcn_arg->fcn_arg_node.arg_sym = strdup($2.Head->var_node.var_sym);
					fcn_arg->fcn_arg_node.arg_type = $2.Head->var_node.varType;
					fcn_arg->fcn_arg_node.next_arg = NULL;
					$$.Head = $$.Tail = fcn_arg;
				}
			}
			else 
				$$.Head = $$.Tail = NULL;
		}
	|declaration_specifiers abstract_declarator {}
	|declaration_specifiers {}
	;
identifier_list:
	IDENT
	|identifier_list ',' IDENT
	;
initializer:
	assignment_expression
	|'{' initializer_list '}'
	|'{' initializer_list ','  '}'
	;
initializer_list:
	initializer
	|designation initializer
	|initializer_list ',' designation initializer
	|initializer_list ',' initializer
	;
designation:
	designator_list '='
	;
designator_list:
	designator
	|designator_list designator
	;
designator:
	'[' constant_expression ']'
	|'.' IDENT
	;
type_name:
	specifier_qualifier_list abstract_declarator
	|specifier_qualifier_list
	;
abstract_declarator:
	pointer { }
	|pointer direct_abstract_declarator { }
	|direct_abstract_declarator {}
	;
direct_abstract_declarator:
	'(' abstract_declarator ')' {}
	|direct_abstract_declarator '[' assignment_expression ']' {}
	|'[' assignment_expression']' {}
	|direct_abstract_declarator '[' ']' {printf("abstract_declarator\n");}
	|'[' ']' {printf("abstract_declarator\n");}
	|direct_abstract_declarator '[' '*' ']' {}
	|'[' '*' ']' {}
	|direct_abstract_declarator '(' parameter_type_list ')' {}
	|'(' parameter_type_list ')' {}
	|direct_abstract_declarator '(' ')' {}
	|'(' ')' { printf("abstract_declarator\n");}
	;
/*	
typedef_name:
	IDENT
	;
*/
statement:
	labeled_statement {}
	|expression_statement {$$.Head = $1.Head;}
	|compound_statement {} 
	|selection_statement {/*$$.Head = $1.Head;*/}
	|iteration_statement {$$.Head = $1.Head; astnode_print($1.Head, 0);}
	|jump_statement {}
	;
labeled_statement:
	IDENT ':' statement
	|CASE constant_expression ':' statement
	|DEFAULT ':' statement
	;
selection_statement:
	IF '(' expression ')' statement 
		{
			// $$.Head = $$.Tail = ast_newnode(AST_IF);
			// $$.Head->if_node.test = $3.Head;
			// $$.Head->if_node.true = $5.Head;
		}
	|IF '(' expression ')' statement ELSE statement
		{
			// $$.Head = $$.Tail = ast_newnode(AST_IF);
			// $$.Head->if_node.test = $3.Head;
			// $$.Head->if_node.true = $5.Head;
			// $$.Head->if_node.false = $7.Head;
		}
	|SWITCH '(' expression ')' statement
	;
iteration_statement:
	WHILE '(' expression ')' statement
		{
			// $$.Head = $$.Tail = ast_newnode(AST_WHILE);
			// $$.Head->while_node.test = $3.Head;
			// $$.Head->while_node.body = $5.Head;
		}
	|DO statement WHILE '('expression')' ';' {}
	|FOR '(' ';' ';' ')' statement { /*$$.Head = $$.Tail = ast_newnode(AST_FOR); $$.Head->for_node.body = $6.Head;*/}
	|FOR '(' ';' ';' expression ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR); 
			// $$.Head->for_node.incr = $5.Head;
			// $$.Head->for_node.body = $7.Head;
		}
	|FOR '(' ';' expression ';' ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR); 
			// $$.Head->for_node.cond = $4.Head;
			// $$.Head->for_node.body = $7.Head;
		}
	|FOR '(' ';' expression ';' expression ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR);
			// $$.Head->for_node.cond = $4.Head;
			// $$.Head->for_node.incr = $6.Head;
			// $$.Head->for_node.body = $8.Head;
		}
	|FOR '(' expression ';' ';' ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR);
			// $$.Head->for_node.init = $3.Head;
			// $$.Head->for_node.body = $7.Head;
		}
	|FOR '(' expression ';' ';' expression ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR);
			// $$.Head->for_node.init = $3.Head;
			// $$.Head->for_node.incr = $6.Head;
			// $$.Head->for_node.body = $8.Head;
		}
	|FOR '(' expression ';' expression ';' ')' statement
		{ 
			// $$.Head = $$.Tail = ast_newnode(AST_FOR);
			// $$.Head->for_node.init = $3.Head;
			// $$.Head->for_node.cond = $5.Head;
			// $$.Head->for_node.body = $8.Head;
		}
	|FOR '(' expression ';' expression ';' expression ')' statement
		{ 
			$$.Head = $$.Tail = ast_newnode(AST_FOR);
			$$.Head->for_node.init = $3.Head;
			$$.Head->for_node.cond = $5.Head;
			$$.Head->for_node.incr = $7.Head;
			$$.Head->for_node.body = $9.Head;
		}
  |FOR '(' declaration ';' ';' ')' statement {}
	|FOR '(' declaration ';' ';' expression ')' statement {}   
	|FOR '(' declaration ';' expression ';' ')' statement {}  
	|FOR '(' declaration ';' expression ';' expression ')' statement {}
	|FOR '(' declaration expression ';' ';' ')' statement {}
	|FOR '(' declaration expression ';' ';' expression ')' statement {}
	|FOR '(' declaration expression ';' expression ';' ')' statement {}
	|FOR '(' declaration expression ';' expression ';' expression ')' statement {}
	;
jump_statement:
	GOTO IDENT ';'
	|CONTINUE ';'
	|BREAK ';'
	|RETURN expression ';'
	|RETURN ';'
	;
expression_statement:
	expression ';'
		{
			 // astnode_print($1.Head, 0);
			 // $$.Head = $$.Tail = $1.Head;
		}
	|';' {}
	;
compound_statement:
	'{' 
		{			
			if (isBlockScope == 1) {
				push_new_scope(SCOPE_STACK);
				SCOPE_STACK->end->scopeType = _BLOCK;
			}
			isBlockScope = 1;
		}
		block_item_list '}' { isBlockScope = 0; pop_curr_scope(SCOPE_STACK);}
	|'{' '}'  { pop_curr_scope(SCOPE_STACK); }
	;
block_item_list:
	block_item {/*printf("1st block list \n");*/}
	|block_item_list block_item
	;
block_item:
	declaration
	|statement {/*astnode_print($1.Head, 0);*/}
	;
expression:
	assignment_expression {}
	|expression ',' assignment_expression {}
	;
assignment_expression:
	conditional_expression {$$.Head = $1.Head;}
	|unary_expression assignment_operator assignment_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = $$.Tail = ast_newnode(AST_ASS);
				astnode *operation = ast_newnode(AST_BINOP); 
				$$.Head->equals_node.lval = $1.Head;
				switch($2) {
					case '=':
						$$.Head->equals_node.rval = $3.Head;
						break;
					case TIMESEQ:
						operation->binop_node.op_type = strdup("*");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case DIVEQ:
						operation->binop_node.op_type = strdup("/");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case MODEQ:
						operation->binop_node.op_type = strdup("%");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case PLUSEQ:
						operation->binop_node.op_type = strdup("+");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case MINUSEQ:
						operation->binop_node.op_type = strdup("-");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case SHREQ:
						operation->binop_node.op_type = strdup(">>");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case SHLEQ:
						operation->binop_node.op_type = strdup("<<");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case ANDEQ:
						operation->binop_node.op_type = strdup("&");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case XOREQ:
						operation->binop_node.op_type = strdup("^");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
					case OREQ:
						operation->binop_node.op_type = strdup("|");
						operation->binop_node.left_op = $1.Head; operation->binop_node.right_op = $3.Head;
						$$.Head->equals_node.rval = operation;
						break;
				}
			}
		}
	;
assignment_operator:
	'=' 				{$$ = '=';}
	|TIMESEQ 		{$$ = TIMESEQ;}
	|DIVEQ			{$$ = DIVEQ;}
	|MODEQ 			{$$ = MODEQ;}
	|PLUSEQ 		{$$ = PLUSEQ;}
	|MINUSEQ 		{$$ = MINUSEQ;}
	|SHREQ 			{$$ = SHREQ;}
	|SHLEQ			{$$ = SHLEQ;}
	|ANDEQ 			{$$ = ANDEQ;}
	|XOREQ 			{$$ = XOREQ;}
	|OREQ 			{$$ = OREQ;}
	;
constant_expression:
	conditional_expression {$$.Head = $1.Head;}
	;
conditional_expression:
	logical_OR_expression {$$.Head = $1.Head;}
	|logical_OR_expression '?' expression ':' conditional_expression
		{
		}
	;
logical_OR_expression:
	logical_AND_expression {$$.Head = $1.Head;}
	|logical_OR_expression LOGOR logical_AND_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "||";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
logical_AND_expression:
	inclusive_OR_expression {$$.Head = $1.Head;}
	|logical_AND_expression LOGAND inclusive_OR_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "&&";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
inclusive_OR_expression:
	exclusive_OR_expression {$$.Head = $1.Head;}
	|inclusive_OR_expression '|' exclusive_OR_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "|";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
exclusive_OR_expression:
	AND_expression {$$.Head = $1.Head;}
	|exclusive_OR_expression '^' AND_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "^";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
AND_expression:
	equality_expression {$$.Head = $1.Head;}
	|AND_expression '&' equality_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "&";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
equality_expression:
	relational_expression {$$.Head = $1.Head;}
	|equality_expression EQEQ relational_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "==";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|equality_expression NOTEQ relational_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "!=";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
relational_expression:
	shift_expression {$$.Head = $1.Head;}
	|relational_expression '<' shift_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "<";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|relational_expression '>' shift_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = ">";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|relational_expression LTEQ shift_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "<=";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|relational_expression GTEQ shift_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = ">=";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
shift_expression:
	additive_expression {$$.Head = $1.Head;}
	|shift_expression SHL additive_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "<<";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|shift_expression SHR additive_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = ">>";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
additive_expression:
	multiplicative_expression {$$.Head = $1.Head;}
	|additive_expression '+' multiplicative_expression 
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "+";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|additive_expression '-' multiplicative_expression 
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "-";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
multiplicative_expression:
	cast_expression {$$.Head = $1.Head;}
	|multiplicative_expression '*' cast_expression 
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "*";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|multiplicative_expression '/' cast_expression
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "/";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	|multiplicative_expression '%' cast_expression 
		{
			if ($1.Head != NULL && $3.Head != NULL) {
				$$.Head = ast_newnode(AST_BINOP);
				$$.Head->binop_node.op_type = "%";
				$$.Head->binop_node.left_op = $1.Head;
				$$.Head->binop_node.right_op = $3.Head;
			}	else $$.Head = NULL;
		}
	;
cast_expression:
	unary_expression {$$.Head = $1.Head;}
	|'(' type_name ')' cast_expression {}
	;
unary_expression:
	postfix_expression {$$.Head = $1.Head;}
	|PLUSPLUS unary_expression
		{
			if ($2.Head != NULL) {
				int type = get_astnode_type($2.Head);
				if (type == AST_VAR && get_astnode_type($2.Head->var_node.varType) == AST_SCALAR || type == AST_PTR) {
					$$.Head = $$.Tail = ast_newnode(AST_ASS);
					$$.Head->equals_node.lval = $2.Head;
					astnode *add_1 = ast_newnode(AST_BINOP);
					astnode *number_node = ast_newnode(AST_NUM);
					number_node->num_node.num_type = _I;
					number_node->num_node.val.i = 1;
					add_1->binop_node.left_op = $2.Head;
					add_1->binop_node.right_op = number_node;
					add_1->binop_node.op_type = "+";
					$$.Head->equals_node.rval = add_1;
				}
				else {
					fprintf(stderr, "Error:%s:%d:Wrong type argument to increment\n", filename, lineno);
					$$.Head = $$.Tail = NULL;
				}
			} else $$.Head = $2.Head;
		}
	|MINUSMINUS unary_expression
		{
			if ($2.Head != NULL) {
				int type = get_astnode_type($2.Head);
				if (type == AST_VAR && get_astnode_type($2.Head->var_node.varType) == AST_SCALAR || type == AST_PTR) {
					$$.Head = $$.Tail = ast_newnode(AST_ASS);
					$$.Head->equals_node.lval = $2.Head;
					astnode *sub_1 = ast_newnode(AST_BINOP);
					astnode *number_node = ast_newnode(AST_NUM);
					number_node->num_node.num_type = _I;
					number_node->num_node.val.i = 1;
					sub_1->binop_node.left_op = $2.Head;
					sub_1->binop_node.right_op = number_node;
					sub_1->binop_node.op_type = "-";
					$$.Head->equals_node.rval = sub_1;
				}
				else {
					fprintf(stderr, "Error:%s:%d:Wrong type argument to increment\n", filename, lineno);
					$$.Head = $$.Tail = NULL;
				}
			} else $$.Head = $2.Head;
		}
	|unary_operator cast_expression
		{
			if ($2.Head != NULL) {
				int expr_type = get_astnode_type($2.Head);
				switch($1) {
					case '&': //&(non_arr_type) -> ptr to (non_arr_type)
						if (expr_type == AST_PTR && get_astnode_type($2.Tail->var_node.varType) == AST_ARR) {
							astnode *pointer = ast_newnode(AST_PTR); 
							pointer->ptr_node.baseType = $2.Tail->var_node.varType; //int a[12], &a -> ptr to arr(12)
							$$.Head = $$.Tail = pointer;
						} //&(function) -> error (we're not allowing it here)
						else if (expr_type == AST_PTR && get_astnode_type($2.Tail) == AST_FCN) { 
							fprintf(stderr, "Error:%s:%d:Attempting to take address of function\n", filename, lineno);
							$$.Head = $$.Tail = NULL;
						}
						else { //everything else
							if (expr_type == AST_NUM) { //basic error checking to prevent taking address of rvals that are #s
								fprintf(stderr, "Error:%s:%d:Argument to & must be lval\n", filename, lineno);
								$$.Head = $$.Tail = NULL;
							} else {
								$$.Head = $$.Tail = ast_newnode(AST_PTR);
								$$.Head->ptr_node.baseType = $2.Head;
							}
						}
						astnode_print($$.Head, 0);
						break;
					case '*':
						if (expr_type == AST_PTR) {
							$$.Head = $$.Tail = ast_newnode(AST_DEREF);
							$$.Head->deref_node.underlyingType = $2.Head->ptr_node.baseType;
							astnode_print($$.Head, 0);
						} else {
							fprintf(stderr, "Error:%s:%d:Argument to * must be of pointer type\n", filename, lineno);
							$$.Head = $$.Tail = NULL;
						}
						break;
					case '+':
						break;
					case '-':
						break;
					case '~':
						break;
					case '!':
						break;
				}
			}
		}
	|SIZEOF unary_expression 
		{

		}
	|SIZEOF '(' type_name ')' {}
	;
unary_operator:
	'&'  { $$ = '&'; }
	|'*' { $$ = '*'; }
	|'+' { $$ = '+'; }
	|'-' { $$ = '-'; }
	|'~' { $$ = '~'; }
	|'!' { $$ = '!'; }
	;
postfix_expression:
	primary_expression
		{ $$.Head = $1.Head; $$.Tail = $1.Tail;}
	|postfix_expression '[' expression ']' 
		{
			//$1 must be of ptr type and $3 must be of integer type (number for our compiler)
			//technically the reverse is also true, but we'll disallow that since it's unconvetional
			if ($1.Head != NULL && $3.Head != NULL) {
				if (get_astnode_type($1.Head) != AST_PTR || get_astnode_type($3.Head) != AST_NUM) {
					fprintf(stderr, "Error:%s:%d:Inproper use of array subscripting\n", filename, lineno);
					$$.Head = $$.Tail = NULL;
				}
				else {
					$$.Head = $$.Tail = ast_newnode(AST_DEREF);
					astnode *ptr_add = ast_newnode(AST_BINOP);
					ptr_add->binop_node.op_type = "+"; ptr_add->binop_node.left_op = $1.Head; 
					ptr_add->binop_node.right_op = $3.Head; 
					$$.Head->deref_node.underlyingType = $1.Head->ptr_node.baseType;
				}
			}
		}
	|postfix_expression '('argument_expression_list')' {}
	|postfix_expression '(' ')' {}
	|postfix_expression PLUSPLUS
		{
			if ($1.Head != NULL) {
				int expr_type = get_astnode_type($1.Head); //check for scalar or pointer type
				if (expr_type == AST_SCALAR || expr_type == AST_PTR) {
					$$.Head = $$.Tail = ast_newnode(AST_ASS);
					$$.Head->equals_node.lval = $1.Head;
					astnode *add_1 = ast_newnode(AST_BINOP);
					astnode *number_node = ast_newnode(AST_NUM);
					number_node->num_node.num_type = _I;
					number_node->num_node.val.i = 1;
					add_1->binop_node.left_op = $1.Head;
					add_1->binop_node.right_op = number_node;
					add_1->binop_node.op_type = "+";
					$$.Head->equals_node.rval = add_1;
				}
				else {
					fprintf(stderr, "Error:%s:%d:Wrong type argument to increment\n", filename, lineno);
					$$.Head = $$.Tail = NULL;
				}
			}
			else $$.Head = $$.Tail = $1.Head;
		}
	|postfix_expression MINUSMINUS
		{
			if ($1.Head != NULL) {
				int expr_type = get_astnode_type($1.Head);
				if (expr_type == AST_SCALAR || expr_type == AST_PTR) {
					$$.Head = $$.Tail = ast_newnode(AST_ASS);
					$$.Head->equals_node.lval = $1.Head;
					astnode *sub_1 = ast_newnode(AST_BINOP);
					astnode *number_node = ast_newnode(AST_NUM);
					number_node->num_node.num_type = _I;
					number_node->num_node.val.i = 1;
					sub_1->binop_node.left_op = $1.Head;
					sub_1->binop_node.right_op = number_node;
					sub_1->binop_node.op_type = "-";
					$$.Head->equals_node.rval = sub_1;
				}
				else {
					fprintf(stderr, "Error:%s:%d:Wrong type argument to increment\n", filename, lineno);
					$$.Head = $$.Tail = NULL;
				}
			}	else $$.Head = $$.Tail = $1.Head;
		}
	|postfix_expression '.' IDENT {}
	|postfix_expression INDSEL IDENT
		{

		}
	|'(' type_name ')' '{' initializer_list '}' {}
	|'(' type_name ')' '{' initializer_list ',' '}' {}
	;
primary_expression:
	IDENT
		{
			symtab *id_tab = getSymbolTable($1.tok, SCOPE_STACK->end, _DEFAULT);
			char *s = $1.tok;
			if (id_tab == NULL) {
				fprintf(stderr, "%s:%d:Error:Undefined symbol %s\n", filename, lineno, s);
				$$.Head = $$.Tail = NULL;
			} 
			else {
				symrec *id_sym = lookup($1.tok, id_tab, _DEFAULT);
				int identType = get_astnode_type(id_sym->ast_node);
				int identVarType = get_astnode_type(id_sym->ast_node->var_node.varType);
				//if var has type array, convert to pointer to element type
				if (identType == AST_VAR && identVarType == AST_ARR) {
					astnode *theArray = id_sym->ast_node->var_node.varType;
					if (theArray->arr_node.etype->scalar_node.scalar_type == _VOID) {
						fprintf(stderr, "%s:%d:Error:Array %s declared as array of voids\n",filename, lineno, s);
						$$.Head = $$.Tail = NULL;
					}
					else {
						astnode *ptrToArrayType = ast_newnode(AST_PTR);
						ptrToArrayType->ptr_node.baseType = theArray->arr_node.etype;
						$$.Head = ptrToArrayType; $$.Tail = id_sym->ast_node;
					}
				}
				//if ident is name of function, convert to pointer to function 
				else if (identType == AST_FCN) {
					astnode *ptrToFunction = ast_newnode(AST_PTR);
					ptrToFunction->ptr_node.baseType = id_sym->ast_node;
					$$.Head = ptrToFunction; $$.Tail = id_sym->ast_node;
				}
				else {
						if (id_sym->ast_node->var_node.varType->scalar_node.scalar_type == _VOID) {
							fprintf(stderr, "%s:%d:Error:Variable %s declared void\n",filename, lineno, s);
							$$.Head = $$.Tail = NULL;
						}
						else {
							$$.Head = id_sym->ast_node->var_node.varType ;$$.Tail = id_sym->ast_node;
						}
				}
			}
		}
	|NUMBER
		{
      $$.Head = $$.Tail = ast_newnode(AST_NUM);
      if (strcmp($1.num_type, "REAL") == 0) {
        fprintf(stderr, "%s:%d:Warning:Truncating real number to integer\n", filename, lineno);
        $$.Head->num_node.val.i = $1.rtokval;
        $$.Head->num_node.num_type = _I;
      }
      else if (strcmp($1.num_type, "INTEGER") == 0) {
        if(strcmp($1.itype, "UNSIGNED,INT") == 0) {
          $$.Head->num_node.val.u = (unsigned) $1.itokval;
          $$.Head->num_node.num_type = _U;
        }
        else if(strcmp($1.itype, "LONG") == 0) {
          $$.Head->num_node.val.l = (long) $1.itokval;
          $$.Head->num_node.num_type = _L;
        }
        else if(strcmp($1.itype, "UNSIGNED,LONG") == 0) {
          $$.Head->num_node.val.ul = (unsigned long) $1.itokval;
          $$.Head->num_node.num_type = _UL;
        }
        else if(strcmp($1.itype, "UNSIGNED,LONGLONG") == 0) {
          $$.Head->num_node.val.ull = (unsigned long long) $1.itokval;
          $$.Head->num_node.num_type = _ULL;
        }
        else if(strcmp($1.itype, "LONGLONG") == 0) {
          $$.Head->num_node.val.ll = (long long) $1.itokval;
          $$.Head->num_node.num_type = _LL;
        }
        else {
          $$.Head->num_node.val.i = (int) $1.itokval;
          $$.Head->num_node.num_type = _I;
        }
      }
		}
	|CHARLIT {}
	|STRING {}
	|'(' expression ')' {$$.Head = $$.Tail = $2.Head;}
	;
argument_expression_list:
	assignment_expression
	|argument_expression_list ',' assignment_expression
	;
%%

void yyerror(const char *s) {
	fprintf(stderr, "%s:%d:Error:%s\n", filename, lineno, s);
}

int main() {
	SCOPE_STACK = (scopeList *) malloc(sizeof(scopeList));
	SCOPE_STACK = init_scopeList(SCOPE_STACK);
	GLOBAL_SCOPE = push_new_scope(SCOPE_STACK);
	SCOPE_STACK->end->scopeType = _FILE;
	yyparse();
	return 0;
}
