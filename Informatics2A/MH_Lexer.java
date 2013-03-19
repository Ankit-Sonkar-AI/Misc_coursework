
// File:   MH_Lexer.java
// Author: John Longley
// Date:   November 2011

// Java template file for lexer component of Informatics 2A Assignment 2 (2011).
// Concerns lexical classes and lexer for the language MH (`Micro-Haskell').


import java.io.* ;

class MH_Lexer extends GenLexer implements LEX_TOKEN_STREAM {

static class VarAcceptor extends GenAcceptor implements DFA {
    public String lexClass() {return "VAR";};
    public int numberOfStates() {return 3;};

    int nextState(int state, char c)
    {
        switch(state)
        {
            case 0: if (CharTypes.isSmall(c)) return 1; else return 2;
            case 1: if (CharTypes.isSmall(c) || CharTypes.isLetter(c) || CharTypes.isDigit(c) || c == '\'') return 1; else return 2;
            default: return 2;
        }
    }

    boolean accepting (int state) {return (state == 1);}
    boolean dead (int state) {return (state == 2);}

}

static class NumAcceptor extends GenAcceptor implements DFA {
    public String lexClass() {return "NUM";};
    public int numberOfStates() {return 3;}

    int nextState(int state, char c)
    {
        switch(state)
        {
            case 0: if (c == '0' || CharTypes.isNonzeroDigit(c)) return 1; else return 2;
            case 1: if (CharTypes.isDigit(c)) return 1; else return 2;
            default: return 2;
        }
    }

    boolean accepting (int state) {return (state == 1);}
    boolean dead (int state) {return (state == 2);}
}

static class BooleanAcceptor extends GenAcceptor implements DFA {
    public String lexClass() {return "BOOLEAN";};
    public int numberOfStates() { return 10 ;} ;

    int nextState(int state, char c)
    {
        switch(state)
        {
            case 0: if (c == 'T') return 1; else if (c == 'F') return 4; else return 9;
            case 1: if (c == 'r') return 2; else return 9;
            case 2: if (c == 'u') return 3; else return 9;
            case 3: if (c == 'e') return 8; else return 9;
            case 4: if (c == 'a') return 5; else return 9;
            case 5: if (c == 'l') return 6; else return 9;
            case 6: if (c == 's') return 7; else return 9;
            case 7: if (c == 'e') return 8; else return 9;
            default: return 9;
        }
    }

    boolean accepting (int state) {return (state == 8) ;}
    boolean dead (int state) {return (state == 9) ;}
}

static class SymAcceptor extends GenAcceptor implements DFA {
    public String lexClass () {return "SYM";};
    public int numberOfStates() {return 3;};


    int nextState(int state, char c) 
    {
        switch(state)
        {
            case 0: if (CharTypes.isSymbolic(c)) return 1; else return 2 ;
            case 1: if (CharTypes.isSymbolic(c)) return 1; else return 2 ;
            default: return 2;
        }
    }

    boolean accepting (int state) {return (state == 1) ;}
    boolean dead (int state) {return (state == 2) ;}

}

static class WhitespaceAcceptor extends GenAcceptor implements DFA {
    public String lexClass () {return "";};
    public int numberOfStates() {return 3;};


    int nextState(int state, char c) 
    {
        switch(state)
        {
            case 0: if (CharTypes.isWhitespace(c)) return 1; else return 2 ;
            case 1: if (CharTypes.isWhitespace(c)) return 1; else return 2 ;
            default: return 2;
        }
    }

    boolean accepting (int state) {return (state == 1) ;}
    boolean dead (int state) {return (state == 2) ;}
}

static class CommentAcceptor extends GenAcceptor implements DFA {
    public String lexClass () {return "";};
    public int numberOfStates() {return 6;};

    int nextState(int state, char c)
    {
        switch(state)
        {
            case 0: if (c == '-') return 1; else return 5;
            case 1: if (c == '-') return 2; else return 5;
            case 2: if (c == '-') return 2; else if (!CharTypes.isSymbolic(c) && c != '\n') return 3; else return 5;
            case 3: if ((c != '\n')) return 3; else if (c == '\n') return 4; else return 5;
            default: return 5;
        }
    }

    boolean accepting (int state) {return (state == 4); }
    boolean dead (int state) {return (state == 5);}
}

static class TokAcceptor extends GenAcceptor implements DFA {

    String tok ;
    int tokLen ;
    String check_tok(String tok)
    {
        if (tok.length() < 7)
        {
            String string = "";
            for(int i = 0; i<7-tok.length(); i++)
            {
                string = string + " ";
            }
            tok = tok + string;
        }
        return tok;
    }

    TokAcceptor (String tok) {this.tok = tok; tokLen = tok.length() ;}
    public String lexClass() {return tok;};
    public int numberOfStates() {return 8;};

       
    int nextState(int state, char c)
    {
        if (state == 0 && tokLen > 1 && tok.charAt(state) == c)
            return 1;
        else if (state == 1 && tok.charAt(state) == c && tokLen == 2)
            return 6;
        else if (state == 1 && tok.charAt(state) == c && tokLen > 2)
            return 2;
        else if (state == 2 && tok.charAt(state) == c)
            return 3;
        else if (state == 3 && tok.charAt(state) == c && tokLen == 4)
            return 6;
        else if (state == 3 && tok.charAt(state) == c && tokLen > 4)
            return 4;
        else if (state == 4 && tok.charAt(state) == c && tokLen > 4)
            return 5;
        else if (state == 5 && tok.charAt(state) == c && tokLen > 4)
            return 6;
        else if (state == 0 && tokLen == 1 && tok.charAt(state) == c)
            return 6;
        else if (state == 6 && tokLen == 7 && tok.charAt(state) == c)
            return 6;
        else if (c == ' ')
            return 7;
        else
            return 7;
    }
   
    boolean accepting (int state) {return (state == 6);}
    boolean dead (int state) {return (state == 7);}
     
}

    static DFA varAcc = new VarAcceptor();
    static DFA numAcc = new NumAcceptor();
    static DFA booleanAcc = new BooleanAcceptor();
    static DFA symAcc = new SymAcceptor();
    static DFA whspAcc = new WhitespaceAcceptor();
    static DFA commentAcc = new CommentAcceptor();
    static DFA IntegerAcc = new TokAcceptor("Integer");
    static DFA BoolAcc = new TokAcceptor("Bool");
    static DFA LBrackAcc = new TokAcceptor("(");
    static DFA RBrackAcc = new TokAcceptor(")");
    static DFA SemiColonAcc = new TokAcceptor(";");
    static DFA IfAcc = new TokAcceptor("if");
    static DFA ElseAcc = new TokAcceptor("else");
    static DFA ThenAcc = new TokAcceptor("then");
    static DFA[] MH_acceptors =
    new DFA[]  {LBrackAcc, RBrackAcc, SemiColonAcc,IntegerAcc, BoolAcc, IfAcc, ElseAcc, ThenAcc, varAcc, numAcc, booleanAcc, symAcc, whspAcc, commentAcc};
    MH_Lexer (Reader reader) {
    super(reader,MH_acceptors) ;
    }

}

class MH_LexerDemo{
    public static void main (String[] args) 
    throws LexError, StateOutOfRange, IOException {
    System.out.print ("Lexer> ") ;
    Reader reader = new BufferedReader (new InputStreamReader (System.in)) ;
    MH_Lexer demoLexer = new MH_Lexer (reader) ;
    LexToken currTok = demoLexer.pullProperToken() ;
    while (currTok != null) {
        System.out.println (currTok.value() + " \t" + 
                currTok.lexClass()) ;
        currTok = demoLexer.pullProperToken() ;
    } ;
    System.out.println ("END OF INPUT.") ;
    }

}
