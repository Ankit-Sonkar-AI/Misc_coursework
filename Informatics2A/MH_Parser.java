
// File:   MH_Parser.java
// Author: John Longley
// Date:   November 2011

// Java template file for parser component of Informatics 2A Assignment 2 (2011).
// Students should add a method body for the LL(1) parse table for Micro-Haskell.


import java.io.* ;
 
class MH_Parser extends GenParser implements PARSER {

    String startSymbol() {return "#Prog" ;}

    // Right hand sides of all productions in grammar:

    String[] epsilon              = new String[] { } ;
    String[] Decl_Prog            = new String[] {"#Decl", "#Prog"} ;
    String[] TypeDecl_TermDecl    = new String[] {"#TypeDecl", "#TermDecl"} ;
    String[] TypeDecl_rule        = new String[] {"VAR", "::", "#Type", ";"} ;
    String[] Type1_TypeOps        = new String[] {"#Type1", "#TypeOps"} ;
    String[] Integer              = new String[] {"Integer"} ;
    String[] Bool                 = new String[] {"Bool"} ;
    String[] lbr_Type_rbr         = new String[] {"(", "#Type", ")"} ;
    String[] arrow_Type           = new String[] {"->", "#Type"} ;
    String[] TermDecl_rule        = new String[] {"VAR", "#Args", "=", 
                          "#Exp", ";"} ;
    String[] VAR_Args             = new String[] {"VAR", "#Args"} ;
    String[] Exp1                 = new String[] {"#Exp1"} ;
    String[] if_then_else_rule    = new String[] {"if", "#Exp", "then", 
                          "#Exp", "else", "#Exp"} ;
    String[] Exp2_Op1             = new String[] {"#Exp2", "#Op1"} ;
    String[] eq_rule              = new String[] {"==", "#Exp2"} ;
    String[] lt_rule              = new String[] {"<", "#Exp2"} ;
    String[] Exp3_Ops2            = new String[] {"#Exp3", "#Ops2"} ;
    String[] plus_rule            = new String[] {"+", "#Exp3", "#Ops2"} ;
    String[] minus_rule           = new String[] {"-", "#Exp3", "#Ops2"} ;
    String[] Exp4_Ops3            = new String[] {"#Exp4", "#Ops3"} ;
    String[] times_rule           = new String[] {"*", "#Exp4", "#Ops3"} ;
    String[] Exp5_Ops4            = new String[] {"#Exp5", "#Ops4"} ;
    String[] VAR                  = new String[] {"VAR"} ;
    String[] NUM                  = new String[] {"NUM"} ;
    String[] BOOLEAN              = new String[] {"BOOLEAN"} ;
    String[] lbr_Exp_rbr          = new String[] {"(", "#Exp", ")"} ;

    String[] tableEntry (String nonterm, String tokClass) {
        if(nonterm.equals("#Prog")){
            if (tokClass==null) return epsilon;
            else if (tokClass.equals("VAR")) return Decl_Prog;
            else if (tokClass.equals("$")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Decl")){
            if (tokClass.equals("VAR")) return TypeDecl_TermDecl;
            else return null;
        }
        if (nonterm.equals("#TypeDecl")){
            if (tokClass.equals("VAR")) return TypeDecl_rule;
            else return null;
        } 
        if(nonterm.equals("#Type")){
            if (tokClass.equals("Integer")) return Type1_TypeOps;
            else if (tokClass.equals("Bool")) return Type1_TypeOps;
            else if (tokClass.equals("(")) return Type1_TypeOps;
            else return null;
        }
        if(nonterm.equals("#Type1")){
            if (tokClass.equals("Integer")) return Integer;
            else if (tokClass.equals("Bool")) return Bool;
            else if (tokClass.equals("(")) return lbr_Type_rbr;
            else return null;
        }
        if(nonterm.equals("#TypeOps")){
            if(tokClass.equals("->")) return arrow_Type;
            else if (tokClass.equals("$")) return epsilon;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals(";")) return epsilon;
            else return null;
        }
        if(nonterm.equals("#TermDecl")){
            if(tokClass.equals("VAR")) return TermDecl_rule;
            else return null;
        }
        if(nonterm.equals("#Args")){
            if(tokClass.equals("VAR")) return VAR_Args;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals("=")) return epsilon;
            else if (tokClass.equals("then")) return epsilon;
            else if (tokClass.equals("else")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Exp")){
            if(tokClass.equals("if")) return if_then_else_rule;
            else if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp1;
            else if (tokClass.equals("(")) return Exp1;
            else return null;
        }
        if (nonterm.equals("#Exp1")){
            if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp2_Op1;
            else if (tokClass.equals("(")) return Exp2_Op1;
            else return null;
        }
        if (nonterm.equals("#Op1")){
            if (tokClass.equals("==")) return eq_rule;
            else if (tokClass.equals("<")) return lt_rule;
            else if (tokClass.equals("(")) return Exp2_Op1;
            else if (tokClass.equals("then")) return epsilon;
            else if (tokClass.equals("else")) return epsilon;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals(";")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Exp2")){
            if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp3_Ops2;
            else if (tokClass.equals("(")) return Exp3_Ops2;
            else return null;
        }
        if (nonterm.equals("#Ops2")){
            if (tokClass.equals("+")) return plus_rule;
            else if (tokClass.equals("-")) return minus_rule;
            else if (tokClass.equals("(")) return Exp3_Ops2;
            else if (tokClass.equals("==")) return epsilon;
            else if (tokClass.equals("<")) return epsilon;
            else if (tokClass.equals("then")) return epsilon;
            else if (tokClass.equals("else")) return epsilon;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals(";")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Exp3")){
            if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp4_Ops3;
            else if (tokClass.equals("(")) return Exp4_Ops3;
            else return null;

        }
        if (nonterm.equals("#Ops3")){
            if (tokClass.equals("*")) return times_rule;
            else if (tokClass.equals("(")) return Exp4_Ops3;
            else if (tokClass.equals("+")) return epsilon;
            else if (tokClass.equals("-")) return epsilon;
            else if (tokClass.equals("==")) return epsilon;
            else if (tokClass.equals("<")) return epsilon;
            else if (tokClass.equals("then")) return epsilon;
            else if (tokClass.equals("else")) return epsilon;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals(";")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Exp4")){
            if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp5_Ops4;
            else if (tokClass.equals("(")) return Exp5_Ops4;
            else return null;
        }
        if (nonterm.equals("#Ops4")){
            if (tokClass.equals("VAR") || tokClass.equals("NUM") || tokClass.equals("BOOLEAN")) return Exp5_Ops4;
            else if (tokClass.equals("(")) return Exp5_Ops4;
            else if (tokClass.equals("+")) return epsilon;
            else if (tokClass.equals("-")) return epsilon;
            else if (tokClass.equals("*")) return epsilon;
            else if (tokClass.equals("==")) return epsilon;
            else if (tokClass.equals("<")) return epsilon;
            else if (tokClass.equals("then")) return epsilon;
            else if (tokClass.equals("else")) return epsilon;
            else if (tokClass.equals(")")) return epsilon;
            else if (tokClass.equals(";")) return epsilon;
            else return null;
        }
        if (nonterm.equals("#Exp5")){
            if (tokClass.equals("VAR")) return VAR;
            else if (tokClass.equals("NUM")) return NUM;
            else if (tokClass.equals("BOOLEAN")) return BOOLEAN;
            else if (tokClass.equals("(")) return lbr_Exp_rbr;
            else return null;
        }
        
        else return null;
    }
}


// For testing

class MH_ParserDemo {

    static PARSER MH_Parser = new MH_Parser() ;

    public static void main (String[] args) throws Exception {
    Reader reader = new BufferedReader (new FileReader (args[0])) ;
    LEX_TOKEN_STREAM MH_Lexer = 
        new CheckedSymbolLexer (new MH_Lexer (reader)) ;
    TREE theTree = MH_Parser.parseTokenStream (MH_Lexer) ;
    }
}
