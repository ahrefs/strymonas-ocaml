(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
(* cabs -- abstract syntax for FrontC                                 
**
** Project:	frontc
** File:	cabs.ml
** Version:	2.1
** Date:	4.7.99
** Author:	Hugues Cass�
**
** 1.0	2.19.99	Hugues Cass�	First version.
** 2.0	3.22.99	Hugues Cass�	Generalization of typed names.
** 2.1	4.7.99	Hugues Cass�	GNU Statement embedded in expressions managed.
*)

(**
 **  Changes for COMP511 project:
 **   - Add #include directive.
 **  - #ifdef and #endif
 **)

let version = "Cabs 2.1 4.7.99 Hugues Cass�"

(*
** Types
*)

type cabsloc = {
 lineno : int;
 filename: string;
 byteno: int;

}                                                                     

let cabslu = {lineno = -10; filename = "cabs loc unknown"; byteno = -10;}

type typeSpecifier = (* Merge all specifiers into one type *)
    Tvoid                             (* Type specifier ISO 6.7.2 *)
  | Tchar
  | Tshort
  | Tint
  | Tlong
  | Tint64
  | Tfloat
  | Tdouble
  | Tsigned
  | Tunsigned
  | Tnamed of string
  (* each of the following three kinds of specifiers contains a field 
   * or item list iff it corresponds to a definition (as opposed to
   * a forward declaration or simple reference to the type); they
   * also have a list of __attribute__s that appeared between the
   * keyword and the type name (definitions only) *)
  | Tstruct of string * field_group list option * attribute list
  | Tunion of string * field_group list option * attribute list
  | Tenum of string * enum_item list option * attribute list
  | TtypeofE of expression                      (* GCC __typeof__ *)
  | TtypeofT of specifier * decl_type       (* GCC __typeof__ *)
  | Tvalue

and storage =
    NO_STORAGE | AUTO | STATIC | EXTERN | REGISTER

and funspec = 
    INLINE | VIRTUAL | EXPLICIT

and cvspec =
    CV_CONST | CV_VOLATILE | CV_RESTRICT

(* Type specifier elements. These appear at the start of a declaration *)
(* Everywhere they appear in this file, they appear as a 'spec_elem list', *)
(* which is not interpreted by cabs -- rather, this "word soup" is passed *)
(* on to the compiler.  Thus, we can represent e.g. 'int long float x' even *)
(* though the compiler will of course choke. *)
and spec_elem =
    SpecTypedef          
  | SpecCV of cvspec            (* const/volatile *)
  | SpecAttr of attribute       (* __attribute__ *)
  | SpecStorage of storage
  | SpecInline
  | SpecType of typeSpecifier
  | SpecPattern of string       (* specifier pattern variable *)

(* decided to go ahead and replace 'spec_elem list' with specifier *)
and specifier = spec_elem list


(* Declarator type. They modify the base type given in the specifier. Keep
 * them in the order as they are printed (this means that the top level
 * constructor for ARRAY and PTR is the inner-level in the meaning of the
 * declared type) *)
and decl_type =
 | JUSTBASE                               (* Prints the declared name *)
 | PARENTYPE of attribute list * decl_type * attribute list
                                          (* Prints "(attrs1 decl attrs2)".
                                           * attrs2 are attributes of the
                                           * declared identifier and it is as
                                           * if they appeared at the very end
                                           * of the declarator. attrs1 can
                                           * contain attributes for the
                                           * identifier or attributes for the
                                           * enclosing type.  *)
 | ARRAY of decl_type * attribute list * expression
                                          (* Prints "decl [ attrs exp ]".
                                           * decl is never a PTR. *)
 | PTR of attribute list * decl_type      (* Prints "* attrs decl" *)
 | PROTO of decl_type * single_name list * bool 
                                          (* Prints "decl (args[, ...])".
                                           * decl is never a PTR.*)

(* The base type and the storage are common to all names. Each name might
 * contain type or storage modifiers *)
(* e.g.: int x, y; *)
and name_group = specifier * name list

(* The optional expression is the bitfield *)
and field_group = specifier * (name * expression option) list

(* like name_group, except the declared variables are allowed to have initializers *)
(* e.g.: int x=1, y=2; *)
and init_name_group = specifier * init_name list

(* The decl_type is in the order in which they are printed. Only the name of
 * the declared identifier is pulled out. The attributes are those that are
 * printed after the declarator *)
(* e.g: in "int *x", "*x" is the declarator; "x" will be pulled out as *)
(* the string, and decl_type will be PTR([], JUSTBASE) *)
and name = string * decl_type * attribute list * cabsloc

(* A variable declarator ("name") with an initializer *)
and init_name = name * init_expression

(* Single names are for declarations that cannot come in groups, like
 * function parameters and functions *)
and single_name = specifier * name


and enum_item = string * expression * cabsloc

(*
** Declaration definition (at toplevel)
*)
and definition =
   FUNDEF of single_name * block * cabsloc * cabsloc
 | DECDEF of init_name_group * cabsloc        (* global variable(s), or function prototype *)
 | TYPEDEF of name_group * cabsloc
 | ONLYTYPEDEF of specifier * cabsloc
 | GLOBASM of string * cabsloc
 | PRAGMA of expression * cabsloc
 | INCLUDE of string * cabsloc
 | IFDEF of string * cabsloc
 | ENDIF of cabsloc
 (* toplevel form transformer, from the first definition to the *)
 (* second group of definitions *)
 | TRANSFORMER of definition * definition list * cabsloc
 (* expression transformer: source and destination *)
 | EXPRTRANSFORMER of expression * expression * cabsloc


(* the string is a file name, and then the list of toplevel forms *)
and file = string * definition list


(*
** statements
*)

(* A block contains a list of local label declarations ( GCC's ({ __label__ 
 * l1, l2; ... }) ) , a list of definitions and a list of statements  *)
and block = 
    { blabels: string list;
      battrs: attribute list;
      bdefs: definition list;
      bstmts: statement list 
    } 

and statement =
   NOP of cabsloc
 | COMPUTATION of expression * cabsloc
 | BLOCK of block * cabsloc
 | SEQUENCE of statement * statement * cabsloc
 | IF of expression * statement * statement * cabsloc
 | WHILE of expression * statement * cabsloc
 | DOWHILE of expression * statement * cabsloc
 | FOR of for_clause * expression * expression * statement * cabsloc
 | BREAK of cabsloc
 | CONTINUE of cabsloc
 | RETURN of expression * cabsloc
 | SWITCH of expression * statement * cabsloc
 | CASE of expression * statement * cabsloc
 | CASERANGE of expression * expression * statement * cabsloc
 | DEFAULT of statement * cabsloc
 | LABEL of string * statement * cabsloc
 | GOTO of string * cabsloc
 | COMPGOTO of expression * cabsloc (* GCC's "goto *exp" *)

 | ASM of attribute list * (* typically only volatile and const *)
         string list * (* template *)
       (string * expression) list * (* list of constraints and expressions for 
                                   * outputs *)
       (string * expression) list * (* same for inputs *)
       string list * (* clobbered registers *)
       cabsloc
       
and for_clause = 
   FC_EXP of expression
 | FC_DECL of definition

(*
** Expressions
*)
and binary_operator =
    ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | BAND | BOR | XOR | SHL | SHR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN

and unary_operator =
    MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

and expression =
    NOTHING
  | UNARY of unary_operator * expression
  | LABELADDR of string  (* GCC's && Label *)
  | BINARY of binary_operator * expression * expression
  | QUESTION of expression * expression * expression

   (* A CAST can actually be a constructor expression *)
  | CAST of (specifier * decl_type) * init_expression

    (* There is a special form of CALL in which the function called 
      is
       __builtin_va_arg and the second argument is sizeof(T). This 
       should be printed as just T *)
  | CALL of expression * expression list
  | COMMA of expression list
  | CONSTANT of constant
  | VARIABLE of string
  | EXPR_SIZEOF of expression
  | TYPE_SIZEOF of specifier * decl_type
  | EXPR_ALIGNOF of expression
  | TYPE_ALIGNOF of specifier * decl_type
  | INDEX of expression * expression
  | MEMBEROF of expression * string
  | MEMBEROFPTR of expression * string
  | GNU_BODY of block
  | EXPR_PATTERN of string     (* pattern variable, and name *)

and constant =
  | CONST_INT of string   (* the textual representation *)
  | CONST_FLOAT of string (* the textual representaton *)
  | CONST_CHAR of int64 list
  | CONST_WCHAR of int64 list
  | CONST_STRING of string
  | CONST_WSTRING of int64 list (* List of wide characters.  Since characters
      * may have 16- or 32-bit values, we can't use a string to represent
      * this constant.  The last element in the list is the terminating nul for
      * this literal. *)

and init_expression =
  | NO_INIT
  | SINGLE_INIT of expression
  | COMPOUND_INIT of (initwhat * init_expression) list

and initwhat =
    NEXT_INIT
  | INFIELD_INIT of string * initwhat
  | ATINDEX_INIT of expression * initwhat
  | ATINDEXRANGE_INIT of expression * expression


                                        (* Each attribute has a name and some
                                         * optional arguments *)
and attribute = string * expression list
                                              

(*********** HELPER FUNCTIONS **********)

let missingFieldDecl = ("___missing_field_name", JUSTBASE, [], cabslu)

let rec isStatic = function
    [] -> false
  | (SpecStorage STATIC) :: _ -> true
  | _ :: rest -> isStatic rest

let rec isExtern = function
    [] -> false
  | (SpecStorage EXTERN) :: _ -> true
  | _ :: rest -> isExtern rest

let rec isInline = function
    [] -> false
  | SpecInline :: _ -> true
  | _ :: rest -> isInline rest

let rec isTypedef = function
    [] -> false
  | SpecTypedef :: _ -> true
  | _ :: rest -> isTypedef rest


let get_statementloc (s : statement) : cabsloc =
begin
  match s with
  | NOP(loc) -> loc
  | COMPUTATION(_,loc) -> loc
  | BLOCK(_,loc) -> loc
  | SEQUENCE(_,_,loc) -> loc
  | IF(_,_,_,loc) -> loc
  | WHILE(_,_,loc) -> loc
  | DOWHILE(_,_,loc) -> loc
  | FOR(_,_,_,_,loc) -> loc
  | BREAK(loc) -> loc
  | CONTINUE(loc) -> loc
  | RETURN(_,loc) -> loc
  | SWITCH(_,_,loc) -> loc
  | CASE(_,_,loc) -> loc
  | CASERANGE(_,_,_,loc) -> loc
  | DEFAULT(_,loc) -> loc
  | LABEL(_,_,loc) -> loc
  | GOTO(_,loc) -> loc
  | COMPGOTO (_, loc) -> loc
  | ASM(_,_,_,_,_,loc) -> loc
end

let get_definitionloc (d : definition) : cabsloc =
begin
  match d with
  | FUNDEF(_, _, l, _) -> l
  | DECDEF(_, l) -> l
  | TYPEDEF(_, l) -> l
  | ONLYTYPEDEF(_, l) -> l
  | GLOBASM(_, l) -> l
  | PRAGMA(_, l) -> l
  | INCLUDE(_, l) -> l
  | IFDEF(_, l) -> l
  | ENDIF(l) -> l
  | TRANSFORMER(_, _, l) -> l
  | EXPRTRANSFORMER(_, _, l) -> l
end

let explodeStringToInts (s: string) : int64 list =  
  let rec allChars i acc = 
    if i < 0 then acc
    else allChars (i - 1) (Int64.of_int (Char.code (String.get s i)) :: acc)
  in
  allChars (-1 + String.length s) []

let valueOfDigit chr =
  let int_value = 
    match chr with
      '0'..'9' -> (Char.code chr) - (Char.code '0')
    | 'a'..'z' -> (Char.code chr) - (Char.code 'a') + 10
    | 'A'..'Z' -> (Char.code chr) - (Char.code 'A') + 10
    | _ -> 0
  in Int64.of_int int_value
  

let unSome o =
  match o with
      Some (x) -> x
    | None -> assert false

  let mkCabs_iconst n =
    CONSTANT(CONST_INT (string_of_int n))

  let mkCabs_binop op trans_s eool info =
     BINARY(op,
	 	   (trans_s (unSome (fst (List.nth eool 0))) info),
		   (trans_s (unSome (fst (List.nth eool 1))) info))

  (* Make a simple Cabs declaration: "cabstype varname = expr".
     [Cabs.typeSpecifier -> string -> Cabs.expression -> bool-> Cabs.definition] *)
  let mkCabs_simple_decl cabstype varname expr isconst cbsli=
    let spec = 
      if isconst = true then
	[ SpecCV(CV_CONST); SpecType(cabstype)]
      else
	[SpecType(cabstype)]
    in
    let name = (varname, JUSTBASE, [], cbsli) in 
    let init_expr =
      match expr with 
	  NOTHING -> NO_INIT
	| _ -> SINGLE_INIT(expr)
    in
    let initnmlist = [(name, init_expr)] in
    let initnmgroup = (spec, initnmlist) in
       DECDEF(initnmgroup, cbsli)

  let mkCabs_array_decl1 cabstype varname size cbsli=
    let spec = [SpecType(cabstype)] in
    let decltype = ARRAY(JUSTBASE, [], (mkCabs_iconst size)) in
    let name = (varname, decltype, [], cbsli) in 
    let initnmlist = [(name, NO_INIT)] in
    let initnmgroup = (spec, initnmlist) in
       DECDEF(initnmgroup, cbsli)

  let mkCabs_ptr_decl1 cabstype varname expr cbsli=
    let spec = [SpecType(cabstype)] in
    let decltype = PTR([], JUSTBASE) in
    let name = (varname, decltype, [], cbsli) in 
    let init_expr =
      match expr with 
	  NOTHING -> NO_INIT
	| _ -> SINGLE_INIT(expr)
    in
    let initnmlist = [(name, init_expr)] in
    let initnmgroup = (spec, initnmlist) in
       DECDEF(initnmgroup, cbsli)

  let mkCabs_array_decl2 cabstype varname size1 size2 cbsli=
    let spec = [SpecType(cabstype)] in
    let dtypeinner = ARRAY(JUSTBASE, [], (mkCabs_iconst size1)) in
    let decltype = ARRAY(dtypeinner, [], (mkCabs_iconst size2)) in
    let name = (varname, decltype, [], cbsli) in 
    let initnmlist = [(name, NO_INIT)] in
    let initnmgroup = (spec, initnmlist) in
       DECDEF(initnmgroup, cbsli)

  (* Make a Cabs assignment: "varname = expr".
     [string -> Cabs.expression -> Cabs.expression] *)
  let mkCabs_assignment varname expr =
     BINARY(ASSIGN, VARIABLE(varname), expr)

  let mkCabs_call namestr cabsexpl =
     CALL(VARIABLE(namestr), cabsexpl)

  let mkCabs_block defs stmts =
    { blabels = [];
      battrs = [];
      bdefs = defs;
      bstmts = stmts }

  let mkCabs_fundef rettype fname (args: single_name list) blk cbsli=
    let proto = PROTO(JUSTBASE, args, false) in
      FUNDEF( (rettype, (fname, proto, [], cbsli)),
              blk, cbsli, cbsli)

  let mkCabs_simple_cast cabstype cabsexp cbsli=
    CAST(([SpecType(cabstype)], JUSTBASE), SINGLE_INIT(cabsexp))    
