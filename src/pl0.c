/*
 * PL/0 编译器 - C语言实现
 * 清华大学出版社《编译原理（第3版）》附录A
 * 
 * 移植自 Borland C++ Builder 版本
 * 去除GUI依赖，改为命令行版本
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ========== 常量定义 ========== */
#define AL      10    /* 标识符最大长度 */
#define NORW    19    /* 保留字个数: 14原版 + FOR/TO/DOWNTO/RETURN + ELSE */
#define TXMAX   100   /* 符号表容量 */
#define NMAX    14    /* 数字最大位数 */
#define AMAX    2047  /* 最大地址值 */
#define LEVMAX  3     /* 最大嵌套深度 */
#define CXMAX   200   /* 代码数组大小 */

/* ========== 类型定义 ========== */
typedef enum {
    NUL, IDENT, NUMBER, PLUS, MINUS, TIMES, SLASH, ODDSYM, EQL, NEQ,
    LSS, LEQ, GTR, GEQ, LPAREN, RPAREN, COMMA, SEMICOLON, PERIOD,
    BECOMES, BEGINSYM, ENDSYM, IFSYM, THENSYM, WHILESYM, WRITESYM,
    READSYM, DOSYM, CALLSYM, CONSTSYM, VARSYM, PROCSYM, PROGSYM,
    FORSYM, TOSYM, DOWNTOSYM, RETURNSYM, ELSESYM,
    PE, ME, PP, MM,  /* 复合赋值: += -= 自增自减: ++ -- */
    SYM_COUNT
} SYMBOL;

typedef enum { CONSTANT, VARIABLE, PROCEDUR } OBJECTS;
typedef enum { LIT, OPR, LOD, STO, CAL, INI, JMP, JPC } FCT;

typedef struct {
    FCT F;  /* 功能码 */
    int L;  /* 层差 0..LEVMAX */
    int A;  /* 位移地址 0..AMAX */
} INSTRUCTION;

/* ========== 全局变量 ========== */
char   CH;           /* 当前字符 */
SYMBOL SYM;          /* 当前符号 */
char   ID[AL+1];     /* 当前标识符 */
int    NUM;          /* 当前数字 */
int    CC;           /* 字符计数器 */
int    LL;           /* 行长度 */
int    CX;           /* 代码索引 */
char   LINE[81];
INSTRUCTION CODE[CXMAX];

char   KWORD[NORW+1][AL+1];
SYMBOL WSYM[NORW+1];
SYMBOL SSYM[256];
char   MNEMONIC[8][4];

int    *DECLBEGSYS, *STATBEGSYS, *FACBEGSYS;

typedef struct {
    char NAME[AL+1];
    OBJECTS KIND;
    union {
        int VAL;   /* 常量值 */
        struct { int LEVEL, ADR, SIZE; } vp;  /* 变量/过程 */
    };
} TABLE_ITEM;
TABLE_ITEM TABLE[TXMAX+1];

FILE *FIN, *FOUT;
int ERR;
int ListOn;
int TableOn;

/* ========== 前向声明 ========== */
void expression(int *FSYS, int LEV, int *TX);
void term(int *FSYS, int LEV, int *TX);
void factor(int *FSYS, int LEV, int *TX);

/* ========== 错误处理 ========== */
void Error(int n) {
    int i;
    printf("***");
    for (i = 0; i < CC-1; i++) printf(" ");
    printf("!  %d\n", n);
    if (FOUT) fprintf(FOUT, "***%*c!  %d\n", CC-1, ' ', n);
    ERR++;
}

/* ========== 符号集操作 ========== */
int SymIn(SYMBOL SYM, int *S) {
    return S[SYM];
}

int* SymSetUnion(int *S1, int *S2) {
    int *S = (int*)malloc(sizeof(int) * SYM_COUNT);
    int i;
    for (i = 0; i < SYM_COUNT; i++)
        S[i] = (S1[i] || S2[i]) ? 1 : 0;
    return S;
}

int* SymSetAdd(SYMBOL SY, int *S) {
    int *S1 = (int*)malloc(sizeof(int) * SYM_COUNT);
    int i;
    for (i = 0; i < SYM_COUNT; i++) S1[i] = S[i];
    S1[SY] = 1;
    return S1;
}

int* SymSetNew(SYMBOL a) {
    int *S = (int*)malloc(sizeof(int) * SYM_COUNT);
    int i;
    for (i = 0; i < SYM_COUNT; i++) S[i] = 0;
    S[a] = 1;
    return S;
}

int* SymSetNew2(SYMBOL a, SYMBOL b) {
    int *S = SymSetNew(a);
    S[b] = 1;
    return S;
}

int* SymSetNew3(SYMBOL a, SYMBOL b, SYMBOL c) {
    int *S = SymSetNew2(a, b);
    S[c] = 1;
    return S;
}

int* SymSetNew4(SYMBOL a, SYMBOL b, SYMBOL c, SYMBOL d) {
    int *S = SymSetNew3(a, b, c);
    S[d] = 1;
    return S;
}

int* SymSetNew5(SYMBOL a, SYMBOL b, SYMBOL c, SYMBOL d, SYMBOL e) {
    int *S = SymSetNew4(a, b, c, d);
    S[e] = 1;
    return S;
}

int* SymSetNew6(SYMBOL a, SYMBOL b, SYMBOL c, SYMBOL d, SYMBOL e, SYMBOL f) {
    int *S = SymSetNew5(a, b, c, d, e);
    S[f] = 1;
    return S;
}

int* SymSetNULL(void) {
    return SymSetNew(NUL);
}

/* ========== 词法分析 ========== */
void GetCh() {
    if (CC == LL) {
        if (feof(FIN)) {
            /* 文件结束 */
            CH = ' ';
            LL = 0; CC = 1;  /* 设置为不相等，防止下次再触发 */
            return;
        }
        LL = 0; CC = 0; CH = ' ';
        int ch;
        while ((ch = fgetc(FIN)) != EOF && ch != '\n') {
            LINE[LL++] = ch;
        }
        LINE[LL++] = ' ';
        LINE[LL] = '\0';
        printf("%3d %s\n", CX, LINE);
        if (FOUT) fprintf(FOUT, "%3d %s\n", CX, LINE);
    }
    CH = LINE[CC++];
}

void GetSym() {
    int i, J, K;
    char A[AL+1];
    
    while (CH <= ' ') GetCh();
    
    if (isalpha(CH)) {
        K = 0;
        do {
            if (K < AL) A[K++] = CH;
            GetCh();
        } while (isalnum(CH));
        A[K] = '\0';
        strncpy(ID, A, AL); ID[AL] = '\0';
        
        i = 1; J = NORW;
        do {
            K = (i + J) / 2;
            if (strcmp(ID, KWORD[K]) <= 0) J = K - 1;
            if (strcmp(ID, KWORD[K]) >= 0) i = K + 1;
        } while (i <= J);
        if (i - 1 > J) SYM = WSYM[K];
        else SYM = IDENT;
    }
    else if (isdigit(CH)) {
        K = 0; NUM = 0; SYM = NUMBER;
        do {
            NUM = 10 * NUM + (CH - '0');
            K++; GetCh();
        } while (isdigit(CH));
        if (K > NMAX) Error(30);
    }
    else if (CH == '+') {
        GetCh();
        if (CH == '=') { SYM = PE; GetCh(); }
        else if (CH == '+') { SYM = PP; GetCh(); }
        else SYM = PLUS;
    }
    else if (CH == '-') {
        GetCh();
        if (CH == '=') { SYM = ME; GetCh(); }
        else if (CH == '-') { SYM = MM; GetCh(); }
        else SYM = MINUS;
    }
    else if (CH == ':') {
        GetCh();
        if (CH == '=') { SYM = BECOMES; GetCh(); }
        else SYM = NUL;
    }
    else if (CH == '<') {
        GetCh();
        if (CH == '=') { SYM = LEQ; GetCh(); }
        else if (CH == '>') { SYM = NEQ; GetCh(); }
        else SYM = LSS;
    }
    else if (CH == '>') {
        GetCh();
        if (CH == '=') { SYM = GEQ; GetCh(); }
        else SYM = GTR;
    }
    else { SYM = SSYM[(unsigned char)CH]; GetCh(); }
}

/* ========== 代码生成 ========== */
void GEN(FCT X, int Y, int Z) {
    if (CX > CXMAX) {
        printf("PROGRAM TOO LONG\n");
        if (FOUT) fprintf(FOUT, "PROGRAM TOO LONG\n");
        if (FOUT) fclose(FOUT);
        exit(0);
    }
    CODE[CX].F = X; CODE[CX].L = Y; CODE[CX].A = Z;
    CX++;
}

void TEST(int *S1, int *S2, int N) {
    if (!SymIn(SYM, S1)) {
        Error(N);
        while (!SymIn(SYM, SymSetUnion(S1, S2))) GetSym();
    }
}

/* ========== 符号表操作 ========== */
void ENTER(OBJECTS K, int LEV, int *TX, int *DX) {
    (*TX)++;
    strncpy(TABLE[*TX].NAME, ID, AL);
    TABLE[*TX].KIND = K;
    switch (K) {
        case CONSTANT:
            if (NUM > AMAX) { Error(31); NUM = 0; }
            TABLE[*TX].VAL = NUM;
            break;
        case VARIABLE:
            TABLE[*TX].vp.LEVEL = LEV;
            TABLE[*TX].vp.ADR = *DX;
            (*DX)++;
            break;
        case PROCEDUR:
            TABLE[*TX].vp.LEVEL = LEV;
            break;
    }
}

int POSITION(char *ID, int TX) {
    int i = TX;
    strcpy(TABLE[0].NAME, ID);
    while (strcmp(TABLE[i].NAME, ID) != 0) i--;
    return i;
}

void ConstDeclaration(int LEV, int *TX, int *DX) {
    if (SYM == IDENT) {
        GetSym();
        if (SYM == EQL || SYM == BECOMES) {
            if (SYM == BECOMES) Error(1);
            GetSym();
            if (SYM == NUMBER) {
                ENTER(CONSTANT, LEV, TX, DX);
                GetSym();
            } else Error(2);
        } else Error(3);
    } else Error(4);
}

void VarDeclaration(int LEV, int *TX, int *DX) {
    if (SYM == IDENT) {
        ENTER(VARIABLE, LEV, TX, DX);
        GetSym();
    } else Error(4);
}

void ListCode(int CX0) {
    int i;
    if (ListOn) {
        for (i = CX0; i < CX; i++)
            printf("%3d %s %d %d\n", i, MNEMONIC[CODE[i].F], CODE[i].L, CODE[i].A);
    }
}

/* ========== 语法分析 ========== */
void factor(int *FSYS, int LEV, int *TX) {
    int i;
    TEST(FACBEGSYS, FSYS, 24);
    while (SymIn(SYM, FACBEGSYS)) {
        if (SYM == IDENT) {
            i = POSITION(ID, *TX);
            if (i == 0) Error(11);
            else
                switch (TABLE[i].KIND) {
                    case CONSTANT: GEN(LIT, 0, TABLE[i].VAL); break;
                    case VARIABLE: GEN(LOD, LEV - TABLE[i].vp.LEVEL, TABLE[i].vp.ADR); break;
                    case PROCEDUR: Error(21); break;
                }
            GetSym();
        } else if (SYM == NUMBER) {
            if (NUM > AMAX) { Error(31); NUM = 0; }
            GEN(LIT, 0, NUM);
            GetSym();
        } else if (SYM == LPAREN) {
            GetSym();
            expression(SymSetAdd(RPAREN, FSYS), LEV, TX);
            if (SYM == RPAREN) GetSym();
            else Error(22);
        }
        TEST(FSYS, FACBEGSYS, 23);
    }
}

void term(int *FSYS, int LEV, int *TX) {
    SYMBOL MULOP;
    factor(SymSetUnion(FSYS, SymSetNew2(TIMES, SLASH)), LEV, TX);
    while (SYM == TIMES || SYM == SLASH) {
        MULOP = SYM; GetSym();
        factor(SymSetUnion(FSYS, SymSetNew2(TIMES, SLASH)), LEV, TX);
        if (MULOP == TIMES) GEN(OPR, 0, 4);
        else GEN(OPR, 0, 5);
    }
}

void expression(int *FSYS, int LEV, int *TX) {
    SYMBOL ADDOP;
    if (SYM == PLUS || SYM == MINUS) {
        ADDOP = SYM; GetSym();
        term(SymSetUnion(FSYS, SymSetNew2(PLUS, MINUS)), LEV, TX);
        if (ADDOP == MINUS) GEN(OPR, 0, 1);
    } else
        term(SymSetUnion(FSYS, SymSetNew2(PLUS, MINUS)), LEV, TX);
    while (SYM == PLUS || SYM == MINUS) {
        ADDOP = SYM; GetSym();
        term(SymSetUnion(FSYS, SymSetNew2(PLUS, MINUS)), LEV, TX);
        if (ADDOP == PLUS) GEN(OPR, 0, 2);
        else GEN(OPR, 0, 3);
    }
}

void condition(int *FSYS, int LEV, int *TX) {
    SYMBOL RELOP;
    if (SYM == ODDSYM) {
        GetSym();
        expression(FSYS, LEV, TX);
        GEN(OPR, 0, 6);
    } else {
        expression(SymSetUnion(SymSetNew6(EQL, NEQ, LSS, LEQ, GTR, GEQ), FSYS), LEV, TX);
        if (!SymIn(SYM, SymSetNew6(EQL, NEQ, LSS, LEQ, GTR, GEQ))) Error(20);
        else {
            RELOP = SYM; GetSym(); expression(FSYS, LEV, TX);
            switch (RELOP) {
                case EQL: GEN(OPR, 0, 8); break;
                case NEQ: GEN(OPR, 0, 9); break;
                case LSS: GEN(OPR, 0, 10); break;
                case GEQ: GEN(OPR, 0, 11); break;
                case GTR: GEN(OPR, 0, 12); break;
                case LEQ: GEN(OPR, 0, 13); break;
                default: break;
            }
        }
    }
}

void statement(int *FSYS, int LEV, int *TX) {
    int i, CX1, CX2;
    switch (SYM) {
        case IDENT:
            i = POSITION(ID, *TX);
            if (i == 0) Error(11);
            else if (TABLE[i].KIND != VARIABLE) { Error(12); i = 0; }
            GetSym();
            if (SYM == BECOMES) GetSym();
            else Error(13);
            expression(FSYS, LEV, TX);
            if (i != 0) GEN(STO, LEV - TABLE[i].vp.LEVEL, TABLE[i].vp.ADR);
            break;
        case READSYM:
            GetSym();
            if (SYM != LPAREN) Error(34);
            else
                do {
                    GetSym();
                    if (SYM == IDENT) i = POSITION(ID, *TX);
                    else i = 0;
                    if (i == 0) Error(35);
                    else {
                        GEN(OPR, 0, 16);
                        GEN(STO, LEV - TABLE[i].vp.LEVEL, TABLE[i].vp.ADR);
                    }
                    GetSym();
                } while (SYM == COMMA);
            if (SYM != RPAREN) {
                Error(33);
                while (!SymIn(SYM, FSYS)) GetSym();
            } else GetSym();
            break;
        case WRITESYM:
            GetSym();
            if (SYM == LPAREN) {
                do {
                    GetSym();
                    expression(SymSetUnion(SymSetNew2(RPAREN, COMMA), FSYS), LEV, TX);
                    GEN(OPR, 0, 14);
                } while (SYM == COMMA);
                if (SYM != RPAREN) Error(33);
                else GetSym();
            }
            GEN(OPR, 0, 15);
            break;
        case CALLSYM:
            GetSym();
            if (SYM != IDENT) Error(14);
            else {
                i = POSITION(ID, *TX);
                if (i == 0) Error(11);
                else if (TABLE[i].KIND == PROCEDUR)
                    GEN(CAL, LEV - TABLE[i].vp.LEVEL, TABLE[i].vp.ADR);
                else Error(15);
                GetSym();
            }
            break;
        case IFSYM: {
            int *nxtlev;
            GetSym();
            /* IF-ELSE: 条件判断后可能跟 THEN 或 ELSE */
            nxtlev = SymSetUnion(SymSetNew3(THENSYM, ELSESYM, DOSYM), FSYS);
            condition(nxtlev, LEV, TX);
            if (SYM == THENSYM) GetSym();
            else Error(16);
            CX1 = CX; GEN(JPC, 0, 0);  /* 条件假时跳转到ELSE或跳过IF块 */
            /* THEN 语句: follow set 必须包含 ELSESYM */
            nxtlev = SymSetAdd(ELSESYM, FSYS);
            statement(nxtlev, LEV, TX);
            if (SYM == ELSESYM) {
                CX2 = CX; GEN(JMP, 0, 0);  /* 跳过ELSE块 */
                CODE[CX1].A = CX;  /* JPC跳转到ELSE */
                GetSym();
                statement(FSYS, LEV, TX);  /* ELSE 语句 */
                CODE[CX2].A = CX;  /* JMP跳转到IF结束后 */
            } else {
                CODE[CX1].A = CX;  /* 无ELSE时，JPC跳转到IF结束后 */
            }
            break;
        }
        case BEGINSYM:
            GetSym();
            statement(SymSetUnion(SymSetNew2(SEMICOLON, ENDSYM), FSYS), LEV, TX);
            while (SymIn(SYM, SymSetAdd(SEMICOLON, STATBEGSYS))) {
                if (SYM == SEMICOLON) GetSym();
                else Error(10);
                statement(SymSetUnion(SymSetNew2(SEMICOLON, ENDSYM), FSYS), LEV, TX);
            }
            if (SYM == ENDSYM) GetSym();
            else Error(17);
            break;
        case WHILESYM:
            CX1 = CX; GetSym();
            condition(SymSetAdd(DOSYM, FSYS), LEV, TX);
            CX2 = CX; GEN(JPC, 0, 0);
            if (SYM == DOSYM) GetSym();
            else Error(18);
            statement(FSYS, LEV, TX);
            GEN(JMP, 0, CX1);
            CODE[CX2].A = CX;
            break;
        default:
            break;
    }
    TEST(FSYS, SymSetNULL(), 19);
}

void Block(int LEV, int TX, int *FSYS) {
    int DX = 3;
    int TX0 = TX;
    int CX0 = CX;
    TABLE[TX].vp.ADR = CX;
    GEN(JMP, 0, 0);
    if (LEV > LEVMAX) Error(32);
    
    do {
        if (SYM == CONSTSYM) {
            GetSym();
            do {
                ConstDeclaration(LEV, &TX, &DX);
                while (SYM == COMMA) { GetSym(); ConstDeclaration(LEV, &TX, &DX); }
                if (SYM == SEMICOLON) GetSym();
                else Error(5);
            } while (SYM == IDENT);
        }
        if (SYM == VARSYM) {
            GetSym();
            do {
                VarDeclaration(LEV, &TX, &DX);
                while (SYM == COMMA) { GetSym(); VarDeclaration(LEV, &TX, &DX); }
                if (SYM == SEMICOLON) GetSym();
                else Error(5);
            } while (SYM == IDENT);
        }
        while (SYM == PROCSYM) {
            GetSym();
            if (SYM == IDENT) { ENTER(PROCEDUR, LEV, &TX, &DX); GetSym(); }
            else Error(4);
            if (SYM == SEMICOLON) GetSym();
            else Error(5);
            Block(LEV+1, TX, SymSetAdd(SEMICOLON, FSYS));
            if (SYM == SEMICOLON) {
                GetSym();
                TEST(SymSetUnion(SymSetNew2(IDENT, PROCSYM), STATBEGSYS), FSYS, 6);
            } else Error(5);
        }
        TEST(SymSetAdd(IDENT, STATBEGSYS), DECLBEGSYS, 7);
    } while (SymIn(SYM, DECLBEGSYS));
    
    CODE[TABLE[TX0].vp.ADR].A = CX;
    TABLE[TX0].vp.ADR = CX;
    TABLE[TX0].vp.SIZE = DX;
    GEN(INI, 0, DX);
    statement(SymSetUnion(SymSetNew2(SEMICOLON, ENDSYM), FSYS), LEV, &TX);
    GEN(OPR, 0, 0);
    TEST(FSYS, SymSetNULL(), 8);
    ListCode(CX0);
}

/* ========== 解释器 ========== */
int BASE_(int L, int B, int *S) {
    int B1 = B;
    while (L > 0) { B1 = S[B1]; L--; }
    return B1;
}

void Interpret() {
    const int STACKSIZE = 500;
    int P, B, T;
    INSTRUCTION I;
    int S[STACKSIZE];
    
    printf("\n=== RUN PL0 ===\n");
    if (FOUT) fprintf(FOUT, "\n=== RUN PL0 ===\n");
    T = 0; B = 1; P = 0;
    S[1] = 0; S[2] = 0; S[3] = 0;
    
    do {
        I = CODE[P]; P++;
        switch (I.F) {
            case LIT: T++; S[T] = I.A; break;
            case OPR:
                switch (I.A) {
                    case 0: T = B - 1; P = S[T + 3]; B = S[T + 2]; break;
                    case 1: S[T] = -S[T]; break;
                    case 2: T--; S[T] = S[T] + S[T + 1]; break;
                    case 3: T--; S[T] = S[T] - S[T + 1]; break;
                    case 4: T--; S[T] = S[T] * S[T + 1]; break;
                    case 5: T--; S[T] = S[T] / S[T + 1]; break;
                    case 6: S[T] = (S[T] % 2 != 0); break;
                    case 8: T--; S[T] = (S[T] == S[T+1]); break;
                    case 9: T--; S[T] = (S[T] != S[T+1]); break;
                    case 10: T--; S[T] = (S[T] < S[T+1]); break;
                    case 11: T--; S[T] = (S[T] >= S[T+1]); break;
                    case 12: T--; S[T] = (S[T] > S[T+1]); break;
                    case 13: T--; S[T] = (S[T] <= S[T+1]); break;
                    case 14: printf("%d", S[T]); if (FOUT) fprintf(FOUT, "%d", S[T]); T--; break;
                    case 15: printf("\n"); if (FOUT) fprintf(FOUT, "\n"); break;
                    case 16: T++; printf("? "); fflush(stdout);
                             if (FOUT) fprintf(FOUT, "? ");
                             scanf("%d", &S[T]);
                             if (FOUT) fprintf(FOUT, "%d\n", S[T]); break;
                    default: break;
                }
                break;
            case LOD: T++; S[T] = S[BASE_(I.L, B, S) + I.A]; break;
            case STO: S[BASE_(I.L, B, S) + I.A] = S[T]; T--; break;
            case CAL: S[T+1] = BASE_(I.L, B, S); S[T+2] = B; S[T+3] = P;
                      B = T + 1; P = I.A; break;
            case INI: T = T + I.A; break;
            case JMP: P = I.A; break;
            case JPC: if (S[T] == 0) P = I.A; T--; break;
            default: break;
        }
    } while (P != 0);
    
    printf("=== END PL0 ===\n");
    if (FOUT) fprintf(FOUT, "=== END PL0 ===\n");
}

/* ========== 主函数 ========== */
int main(int argc, char *argv[]) {
    int i;
    char fname[256] = "";
    char outname[256] = "";
    
    for (i = 0; i < 256; i++) SSYM[i] = NUL;
    
    /* 保留字表 (按字母顺序排列以便二分查找) */
    strcpy(KWORD[ 1], "BEGIN");    strcpy(KWORD[ 2], "CALL");
    strcpy(KWORD[ 3], "CONST");    strcpy(KWORD[ 4], "DO");
    strcpy(KWORD[ 5], "DOWNTO");   strcpy(KWORD[ 6], "ELSE");
    strcpy(KWORD[ 7], "END");      strcpy(KWORD[ 8], "FOR");
    strcpy(KWORD[ 9], "IF");       strcpy(KWORD[10], "ODD");
    strcpy(KWORD[11], "PROCEDURE");strcpy(KWORD[12], "PROGRAM");
    strcpy(KWORD[13], "READ");     strcpy(KWORD[14], "RETURN");
    strcpy(KWORD[15], "THEN");     strcpy(KWORD[16], "TO");
    strcpy(KWORD[17], "VAR");      strcpy(KWORD[18], "WHILE");
    strcpy(KWORD[19], "WRITE");
    
    /* 保留字符号 (与KWORD顺序对应) */
    WSYM[ 1] = BEGINSYM;   WSYM[ 2] = CALLSYM;
    WSYM[ 3] = CONSTSYM;   WSYM[ 4] = DOSYM;
    WSYM[ 5] = DOWNTOSYM;  WSYM[ 6] = ELSESYM;
    WSYM[ 7] = ENDSYM;     WSYM[ 8] = FORSYM;
    WSYM[ 9] = IFSYM;       WSYM[10] = ODDSYM;
    WSYM[11] = PROCSYM;    WSYM[12] = PROGSYM;
    WSYM[13] = READSYM;    WSYM[14] = RETURNSYM;
    WSYM[15] = THENSYM;    WSYM[16] = TOSYM;
    WSYM[17] = VARSYM;     WSYM[18] = WHILESYM;
    WSYM[19] = WRITESYM;
    
    SSYM['+'] = PLUS;      SSYM['-'] = MINUS;
    SSYM['*'] = TIMES;     SSYM['/'] = SLASH;
    SSYM['('] = LPAREN;    SSYM[')'] = RPAREN;
    SSYM['='] = EQL;       SSYM[','] = COMMA;
    SSYM['.'] = PERIOD;    SSYM['<'] = LSS;    SSYM['>'] = GTR;
    SSYM[';'] = SEMICOLON;
    
    strcpy(MNEMONIC[LIT], "LIT");   strcpy(MNEMONIC[OPR], "OPR");
    strcpy(MNEMONIC[LOD], "LOD");   strcpy(MNEMONIC[STO], "STO");
    strcpy(MNEMONIC[CAL], "CAL");   strcpy(MNEMONIC[INI], "INT");
    strcpy(MNEMONIC[JMP], "JMP");   strcpy(MNEMONIC[JPC], "JPC");
    
    DECLBEGSYS = (int*)malloc(sizeof(int) * SYM_COUNT);
    STATBEGSYS = (int*)malloc(sizeof(int) * SYM_COUNT);
    FACBEGSYS  = (int*)malloc(sizeof(int) * SYM_COUNT);
    for (i = 0; i < SYM_COUNT; i++) {
        DECLBEGSYS[i] = 0; STATBEGSYS[i] = 0; FACBEGSYS[i] = 0;
    }
    DECLBEGSYS[CONSTSYM] = 1;
    DECLBEGSYS[VARSYM] = 1;
    DECLBEGSYS[PROCSYM] = 1;
    STATBEGSYS[BEGINSYM] = 1;
    STATBEGSYS[CALLSYM] = 1;
    STATBEGSYS[IFSYM] = 1;
    STATBEGSYS[WHILESYM] = 1;
    STATBEGSYS[WRITESYM] = 1;
    FACBEGSYS[IDENT] = 1;
    FACBEGSYS[NUMBER] = 1;
    FACBEGSYS[LPAREN] = 1;
    
    ListOn = 1; TableOn = 0;
    
    if (argc < 2) {
        printf("Usage: %s <input.pl0> [-l] [-t]\n", argv[0]);
        printf("  -l  List generated code\n");
        printf("  -t  Print symbol table\n");
        printf("\nPL/0 Compiler (C version)\n");
        printf("From: 清华大学出版社《编译原理》\n");
        return 1;
    }
    
    strncpy(fname, argv[1], sizeof(fname)-1);
    fname[sizeof(fname)-1] = '\0';
    
    for (i = 2; i < argc; i++) {
        if (strcmp(argv[i], "-l") == 0) ListOn = 1;
        else if (strcmp(argv[i], "-t") == 0) TableOn = 1;
    }
    
    FIN = fopen(fname, "r");
    if (!FIN) {
        printf("Cannot open file: %s\n", fname);
        return 1;
    }
    
    strncpy(outname, fname, sizeof(outname)-1);
    outname[sizeof(outname)-1] = '\0';
    char *dot = strrchr(outname, '.');
    if (dot) *dot = '\0';
    strcat(outname, ".cod");
    FOUT = fopen(outname, "w");
    
    printf("=== COMPILE %s ===\n", fname);
    if (FOUT) fprintf(FOUT, "=== COMPILE %s ===\n", fname);
    
    ERR = 0;
    CC = 0; CX = 0; LL = 0; CH = ' ';
    GetSym();
    
    if (SYM != PROGSYM) Error(0);
    else {
        GetSym();
        if (SYM != IDENT) Error(0);
        else {
            GetSym();
            if (SYM != SEMICOLON) Error(5);
            else GetSym();
        }
    }
    
    Block(0, 0, SymSetAdd(PERIOD, SymSetUnion(DECLBEGSYS, STATBEGSYS)));
    
    if (SYM != PERIOD) Error(9);
    
    if (ERR == 0) {
        printf("\n");
        Interpret();
    } else {
        printf("\nERROR IN PL/0 PROGRAM (%d errors)\n", ERR);
        if (FOUT) fprintf(FOUT, "\nERROR IN PL/0 PROGRAM (%d errors)\n", ERR);
    }
    
    if (FOUT) fclose(FOUT);
    fclose(FIN);
    
    return 0;
}
