/*
仅实现加法的翻译模式
start->   DS.
D->B; D
D->ε
B->int L    { L.type := int }|real L    { L.type := real }|char L    { L.type := char }|bool L    { L.type := bool }
L->id   { A.Type := L.type  enter(v.entry,L.type)}  A
A-> ，idA   { A1.Type := A.type  enter(v.entry,A.type)}
A->ε

S→ V := EC { gen( ":=", E.place,0,V.place) } H
H→；S | ε
C-><E|>E|ε
E->T    { R.i:=T.place}      R     {E.place:=R.s}
R->+T    { R1.i:= newtemp; gen( "*", R.i, T.place , R1.i) }     R   {R.s:= R1.s; }|-TR
R-> ε    {Rs=R.i}
T->FP
P->*FP|/FP|ε
F->( E )  { F.place := E.place}
F->id     {F.place:=position (id)}
V->id     {V.place:=position(id)}
*/

#include <stdio.h>
#include<dos.h>
#include<stdlib.h>
#include<string.h>
//#include <iostream.h>
#include<ctype.h>
#include <windows.h>

#define txmax 100    /* 符号表最大容量 */
#define al 10        /* 符号的最大长度 */
#define tvmax 500    /* 最多能够申请的临时变量取值范围[100, tvmax] */
#define norw 4       /* 关键字个数 */
#define cxmax 500   /* 最多的虚拟机代码数 */

int tx;              //名字表指针, 取值范围[0, txmax-1]
int tv ;             //临时变量计数

/* 符号 */
enum symbol {
    nul,         eeof,	ident,         plus,      times,	lparen,divide,sub,morethan,lessthan,
	rparen,    comma,     semicolon,  becomes,  period, realsym,    intsym,charsym,boolsym
};

enum symbol sym;    /* 当前的符号 */
char ch;            /* 获取字符的缓冲区，getch 使用 */
char id[al+1];      /* 当前ident, 多出的一个字节用于存放0 */
char a[al+1];       /* 临时符号, 多出的一个字节用于存放0 */

/* 符号表结构 */
struct tablestruct
{
   char name[al];      /* 名字 */
    enum symbol type;   // 类型
};

struct tablestruct table[txmax]; /* 符号表 */

char word[norw][al];        /* 保留字 */
enum symbol wsym[norw];     /* 保留字对应的符号值 */
enum symbol ssym[256];      /* 单字符的符号值，散列表 */
enum symbol tvtype[501];

int cx;             /* 四元式代码指针, 取值范围[0, cxmax-1]*/
struct instruction
{
    char f[al+1]; /* 操作码 */
    char l[al+1];     /* 左操作数 */
    char r[al+1];     /* 右操作数*/
	char t[al+1];     /* 结果 */
};
struct instruction code[cxmax]; /* 存放虚拟机代码的数组 */

FILE* fin;
FILE* fout;

int getsym();
void enter(enum symbol type);
void init();
int position(char* idt);
int gen(enum symbol op, int arg1, int arg2,int result );     //中间代码分析
void writecode(char *op, char *arg1, char *arg2,char *result );    //写缓存
void  start();
void  D();
void  B();
void L(enum symbol type);
void A(enum symbol type);
void S();
void H();
int C(int Ei);
int E();
int R(int Ri);
int T();
int P(int Pi);
int F();
int V();

 int main()
{
    char filename[20];

	printf("请输入分析的文件名:");
	gets(filename);
	if((fin=fopen(filename,"r"))==NULL)
	{
		printf("不能打开文件.\n");
		exit(0);
	}

    init();                  //初始化
    getsym();                //读第一个单词，将单词类别放入sym中，单字词值放入id中
	start();                //开始按start->DS.  分析

    if (sym==eeof)
	{
		printf("语法正确\n\n如果将中间代码保存到文件请输入文件名，否则回车");
		gets(filename);
		if(strlen(filename)<=0) return 0;
		if((fout=fopen(filename,"w"))==NULL)
		{
			printf("不能打开文件.\n");
			exit(0);
		}
		for (int cx1=0;cx1<cx;cx1++)
			fprintf(fout,"(%s,%s,%s,%s)\n",code[cx1].f,code[cx1].l,code[cx1].r,code[cx1].t);
		return 0;
	}
	else {printf("语法错1:  . 后不能再有句子"); exit(0);}
	fclose(fin);
	fclose(fout);
}

//初始化函数
void init()
{
	int i;

	/* 设置单字符符号 */
	for (i=0; i<=255; i++)
	{
		ssym[i] = nul;            //不正确的单字符符号为nul，先预置初值nul
	}
	ssym['+'] = plus;
	ssym['-'] = sub;
	ssym['*'] = times;
	ssym['/'] = divide;
	ssym['('] = lparen;
	ssym[')'] = rparen;
	ssym['.'] = period;
	ssym[','] = comma;
	ssym[';'] = semicolon;
	ssym['>'] = morethan;
	ssym['<'] = lessthan;

	/* 设置保留字名字 */
	strcpy(&(word[0][0]), "real");
	strcpy(&(word[1][0]), "int");
	strcpy(&(word[2][0]), "char");
	strcpy(&(word[3][0]), "bool");

	/* 设置保留字符号 */
	wsym[0] = realsym;
	wsym[1] = intsym;
	wsym[2] = charsym;
	wsym[3] = boolsym;

	tv=100;           //临时变量指针初值，让Tx和tv的取值没有交集，区别到底是临时变变量和声明的变量
	tx=0;           //表指针初值
	cx=0;     //指令计数器

}

/*
* 词法分析，获取一个符号
*/
int getsym()
{
	int i,k;
	ch=fgetc(fin);

	if (ch==EOF) {sym=eeof; return 0;}         //文件结束

	while (ch==' ' || ch==10 || ch==13 || ch==9)  /* 忽略空格、换行、回车和TAB */
		ch=fgetc(fin);

	if (ch>='a' && ch<='z')
	{           /* 名字或保留字以a..z开头 ，*/
		k = 0;
		do
		{
			if(k<al)                  /* 符号的最大长度为al ，超长就截尾处理*/
			{
				a[k] = ch;
				k++;
			}
			ch=fgetc(fin);
		} while (ch>='a' && ch<='z' || ch>='0' && ch<='9');

		a[k] = 0;
		strcpy(id, a);
		fseek(fin,-1,1);

		for (i=0;i<norw;i++)        /* 搜索当前符号是否为保留字 */
			 if (strcmp(id,word[i]) == 0)
					 break;
		if (i <norw)
		{
			sym = wsym[i];
		}
		else
		{
			sym = ident;          /* 搜索失败则，类型是标识符 */

		}
	}
	else if(ch == ':') /* 检测赋值符号 */
	{
		ch=fgetc(fin);
		if (ch == '=')
		{
			sym = becomes;
		}
		else
		{
			sym = nul;  /* 不能识别的符号 */
		}
	}
	else sym = ssym[ch];     /* 当符号不满足上述条件时，全部按照单字符符号处理 */
	return 0;
}

/*
* 在符号表中加入一项
*/

void enter(enum symbol type)
{
	tx=tx+1;
	if (tx > txmax)
    {
		printf(" 符号表越界 ");           /* 符号表越界 */
		return;
	}
	int i = 0;
	for(i; i < tx; i++)
    {
        if(strcmp(table[i].name,id)==0)
        {
            printf("变量已经声明过！不能重复声明！\n");
            exit(0);
        }
	}
	strcpy(table[tx].name, id); /* 全局变量id中已存有当前名字的名字,Tx为插入当前符号之前表尾指针 */
	table[tx].type = type;

}

/*
* 查找名字的位置.
* 找到则返回在名字表中的位置,否则返回0.
*
* idt:    要查找的名字
* tx:     当前名字表尾指针，全局变量
*/
int position(char* idt)
{
	int i;
	strcpy(table[0].name, idt);
	i = tx;
	while (strcmp(table[i].name, idt) != 0)
	{
		i--;
	}
	return i;
}

/* 中间代码*/
int gen(enum symbol op, int arg1, int arg2,int result )
{
	char temp1[al+1],temp2[al+1],temp3[al+1];
	if(arg1>=100)                            //模拟申请临时变量
	{
		wsprintf(temp1,"T%d",arg1);
	}
	else
	{
		strcpy(temp1, table[arg1].name);
	}
	if(arg2>=100)
	{
		wsprintf(temp2,"T%d",arg2);
	}
	else
	{
		strcpy(temp2, table[arg2].name);
	}
	if(result>=100)
	{
		wsprintf(temp3,"T%d",result);
	}
	else
	{
		strcpy(temp3,table[result].name);
	}
	if(op==becomes)//类型匹配检查
    {
        if(arg1<=100)
        {
            if(table[arg1].type!=table[result].type)
            {
                printf("赋值号左右操作数类型不匹配!");exit(0);
            }
        }
        else if(arg1>100&&arg1<=501)
        {
            if(tvtype[arg1]!=table[result].type)
            {
                printf("赋值号左右操作数类型不匹配!");exit(0);
            }
        }
    }
    else
    {
        if(arg1<=100)
        {
            if(arg2<=100)
            {
                if(table[arg1].type!=table[arg2].type)
                {
                    printf("%d号左右操作数类型不匹配!",op);exit(0);
                }
            }
            else if(arg2>100&&arg2<=501)
            {
                if(table[arg1].type!=tvtype[arg2])
                {
                    printf("%d号左右操作数类型不匹配!",op);exit(0);
                }
            }
        }
        else if(arg1>100&&arg1<=501)
        {
            if(arg2<=100)
            {
                if(tvtype[arg1]!=table[arg2].type)
                {
                    printf("%d号左右操作数类型不匹配!",op);exit(0);
                }
            }
            else if(arg2>100&&arg2<=501)
            {
                if(tvtype[arg1]!=tvtype[arg2])
                {
                    printf("%d号左右操作数类型不匹配!",op);exit(0);
                }
            }
        }
    }
    if(op==becomes)
    {
        if(result<=100)
        {
            if(table[result].type==charsym) {printf("char类型变量不能进行赋值运算!");exit(0);}
        }
        else {printf("赋值号左边不是已声明的变量.");exit(0);}
    }
	if (op==becomes)
	{
		printf("(:=,%s,%s,%s)\n",temp1,temp2,temp3);
		writecode(":=",temp1,temp2,temp3);
	}
	else if (op==plus)                          //+运算
	{
		writecode("+",temp1,temp2,temp3);
		printf("(+,%s,%s,%s)\n",temp1,temp2,temp3);
	}
	else if(op == sub)
    {
        writecode("-",temp1,temp2,temp3);
		printf("(-,%s,%s,%s)\n",temp1,temp2,temp3);
    }
    else if(op == times)
    {
        writecode("*",temp1,temp2,temp3);
		printf("(*,%s,%s,%s)\n",temp1,temp2,temp3);
    }
    else if(op == divide)
    {
        writecode("/",temp1,temp2,temp3);
		printf("(/,%s,%s,%s)\n",temp1,temp2,temp3);
    }
    else if(op == sub)
    {
        writecode("-",temp1,temp2,temp3);
		printf("(-,%s,%s,%s)\n",temp1,temp2,temp3);
    }
    else if(op == morethan)
    {
        writecode(">",temp1,temp2,temp3);
		printf("(>,%s,%s,%s)\n",temp1,temp2,temp3);
    }
    else if(op == lessthan)
    {
        writecode("<",temp1,temp2,temp3);
		printf("(<,%s,%s,%s)\n",temp1,temp2,temp3);
    }

	return 0;
}

//处理代码段
void writecode(char op[al+1], char arg1[al+1], char arg2[al+1],char result[al+1] )
{
	if (cx >= cxmax)
	{
		printf("Program too long"); /* 程序过长 */
		return ;
	}
	strcpy(code[cx].f, op);
	strcpy(code[cx].l,arg1);
	strcpy(code[cx].r,arg2);
	strcpy(code[cx].t,result);
	cx++;
	return ;
}

/*分析产生式     P->DS.   */

void  start()
{
	if (sym==intsym ||sym==realsym ||sym == boolsym ||sym == charsym ||sym==ident)
	{
		D();
		S();
		if (sym==period)
		{
			getsym();
			return;
		}
		else
		{printf("语法错2： 缺少程序结束."); exit(0);}
	}
	else
	{printf("语法错3: 程序只能用int,real,bool,和char开始，而且区分大小写"); exit(0);}
}

/*递归下降分析
D->  B; D
D->ε
*/
void  D()
{
	if (sym==intsym ||sym==realsym ||sym==boolsym ||sym==charsym)
	{
		B();
		if (ch=';')
		{
			getsym();
			D();
		}
		else
		{printf("语法错4:缺少;"); exit(0);}
	}
	else if(sym==ident || sym==period)  return;

	else {printf("语法错5"); exit(0);}
}

/*
B->int L    { L.type := int }|real L    { L.type := real }|char L    { L.type := char }|bool L    { L.type := bool }
*/
void  B()
{
	if (sym==intsym )
	{
		getsym();
		L(intsym);
	}
	else if (sym==realsym)
	{
		getsym();
		L(realsym);
	}
	else if (sym==charsym)
	{
		getsym();
		L(charsym);
	}
	else if (sym==boolsym)
	{
		getsym();
		L(boolsym);
	}
	else
	{printf("语法错6:变量只能用int,real,bool,char声明"); exit(0);}
}

/*
L->   id   { A.Type := L.type  enter(v.entry,L.type)}   A       V.entry通过全局变量tx隐性传递
*/
void L(enum symbol type)
{
	if (sym==ident)
	{
		enter(type);
		getsym();
		A(type);
	}
	else
	{printf("语法错7:变量名有问题"); exit(0);}
}

/*
A-> ，id  A   { A1.Type := A.type  enter(v.entry,A.type)}
A->ε
*/

void A(enum symbol type)
{
	if (sym==comma)          //当前单词为，
	{
		getsym();
		if (sym==ident)
		{
			enter(type);
			getsym();
			A(type);
		}
		else
		{printf("语法错8:一次性声明多个变量中有变量的变量名有问题"); exit(0);}
	}
	else if (sym== semicolon)   return ;//当前单词为；即A的follow集元素，相当于进行A->ε
	else
	{printf("语法错9"); exit(0);}
}

/*
S→ V := EC { gen( ":=", E.place,0,V.place) } H
*/
void S()
{
	int vplace,Eplace,Cplace;
	if (sym==ident)
	{
		vplace=V();
		//getsym();
		if (sym==becomes)     //当前单词为:=
		{
			getsym();
			Eplace=E();
			Cplace=C(Eplace);
            gen(becomes,Cplace,-1,vplace);
            H();
		}
		else
		{printf("语法错10:缺少:="); exit(0);}
	}
	else {printf("语法错11"); exit(0);}
}

/*
H→；S | ε
*/
void H()
{
	if (sym==semicolon)          //当前单词为indent类型
	{
		getsym();
		S();
	}
	else if (sym==period)   return ;
	else
	{printf("语法错12"); exit(0);}
}

/*
C-<E|>E|ε
*/
int C(int Ei)
{
    int Eplace;
    if(sym == lessthan)
    {
        getsym();
        Eplace=E();
        if(Eplace<=100)
        {
            if(table[Eplace].type==boolsym) {printf("bool型数值不能进行关系运算<！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行关系运算<！");exit(0);}
        }
        tv=tv+1;
        tvtype[tv]=boolsym;
        gen(lessthan,Ei,Eplace,tv);
        return tv;
    }
    else if(sym==morethan)
    {
        getsym();
        Eplace=E();
        if(Eplace<=100)
        {
            if(table[Eplace].type==boolsym) {printf("bool型数值不能进行关系运算>！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行关系运算>！");exit(0);}
        }
        tv=tv+1;
        tvtype[tv]=boolsym;
        gen(morethan,Ei,Eplace,tv);
        return tv;
    }
    else if(sym==semicolon||sym==period)
    {
        return Ei;
    }
    else {printf("语法错13");exit(0);}
}
/*
E->T      { R.i:=T.place}      R     {E.place:=R.s}
*/

int E()
{
	int ri,tplace,Rs;
	if (sym==ident || sym== lparen)
	{
		tplace=T();
		ri=tplace;
		Rs=R(ri);
	}
	else
		{printf("语法错14"); exit(0);}
	return Rs;
}

/*
R->+T    { R1.i:= newtemp; gen( "*", R.i, T.place , R1.i) }     R   {R.s:= R1.s; }|-TR
R-> ε    {R.s=R.i}
*/

int R(int Ri)
{
	int Rs,tplace;
	if (sym==plus)
	{
		getsym();
		tplace=T();
		if(tplace<=100)
        {
            if(table[tplace].type==charsym) {printf("char型数值不能进行代数运算+！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char型数值不能进行代数运算+！");exit(0);}
        }
		if(tplace<=100)
        {
            if(table[tplace].type==boolsym) {printf("bool型数值不能进行代数运算+！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行代数运算+！");exit(0);}
        }
        tv=tv+1;            //生成临时变量
        if(tplace<=100)
        {
            tvtype[tv]=table[tplace].type;
        }
        else
        {
            tvtype[tv]=tvtype[tv-1];
        }
        gen(plus,Ri,tplace,tv);
        Rs=R(tv);
	}
	else if(sym == sub)
    {
        getsym();
		tplace=T();
		if(tplace<=100)
        {
            if(table[tplace].type==charsym) {printf("char型数值不能进行代数运算-！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char型数值不能进行代数运算-！");exit(0);}
        }
		if(tplace<=100)
        {
            if(table[tplace].type==boolsym) {printf("bool型数值不能进行代数运算-！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行代数运算-！");exit(0);}
        }
        tv=tv+1;            //生成临时变量
        if(tplace<=100)
        {
            tvtype[tv]=table[tplace].type;
        }
        else
        {
            tvtype[tv]=tvtype[tv-1];
        }
        gen(sub,Ri,tplace,tv);
        Rs=R(tv);
    }
	else if (sym== semicolon || sym==rparen|| sym==period||sym==lessthan||sym==morethan)
	{
		Rs=Ri;
	}
	else {printf("语法错15"); exit(0);}
	return Rs;
}

/*
T->FP
*/
int T()
{
    int pi,fplace,Ps;
    if(sym==ident||sym==lparen)
    {
        fplace=F();
        pi=fplace;
        Ps=P(pi);
    }
    else
        {printf("语法错16"); exit(0);}
	return Ps;
}

/*
P->*FP|/FP|ε
*/
int P(int Pi)
{
    int Ps,fplace;
	if (sym==times)
	{
		getsym();
		fplace=F();
		if(fplace<=100)
        {
            if(table[fplace].type==charsym) {printf("char型数值不能进行代数运算*！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char型数值不能进行代数运算*！");exit(0);}
        }
		if(fplace<=100)
        {
            if(table[fplace].type==boolsym) {printf("bool型数值不能进行代数运算*！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行代数运算*！");exit(0);}
        }
        tv=tv+1;            //生成临时变量
        if(fplace<=100)
        {
            tvtype[tv]=table[fplace].type;
        }
        else
        {
            tvtype[tv]=tvtype[tv-1];
        }
        gen(times,Pi,fplace,tv);
        Ps=P(tv);
	}
	else if(sym==divide)
    {
        getsym();
		fplace=F();
		if(fplace<=100)
        {
            if(table[fplace].type==charsym) {printf("char型数值不能进行代数运算/！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char型数值不能进行代数运算/！");exit(0);}
        }
		if(fplace<=100)
        {
            if(table[fplace].type==boolsym) {printf("bool型数值不能进行代数运算/！");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool型数值不能进行代数运算/！");exit(0);}
        }
        tv=tv+1;            //生成临时变量
        if(fplace<=100)
        {
            tvtype[tv]=table[fplace].type;
        }
        else
        {
            tvtype[tv]=tvtype[tv-1];
        }
        gen(divide,Pi,fplace,tv);
        Ps=P(tv);
    }
	else if (sym== semicolon || sym==rparen|| sym==period||sym==plus||sym==sub||sym==lessthan||sym==morethan)
	{
		Ps=Pi;
	}
	else {printf("语法错17"); exit(0);}
	return Ps;
}

/*

F->( E )  { F.place := E.place}
F->id     {F.place:=position (id)}
*/
int F()
{
	int Fplace;
	if (sym==ident)
	{
		Fplace=position (id);
		if (Fplace==0)  {printf("变量没有声明"); exit(0);}
		getsym();
	}
	else if (sym== lparen)
	{
		getsym();
		Fplace=E();
		if (sym== rparen)
			getsym();
		else
		{
			printf("语法错，缺)"); exit(0);
		}
	}
	else{printf("语法错,缺("); exit(0);}
	return Fplace;
}

/*

V->id     {V.place:=position(id)}
*/
int V()
{
	int Vplace;
	if (sym==ident)
	{
		Vplace=position (id);
		if (Vplace==0)  {printf("变量没有声明"); exit(0);}
		getsym();
	}
	else{printf("语法错18"); exit(0);}
	return Vplace;
}
