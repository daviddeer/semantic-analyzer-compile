/*
��ʵ�ּӷ��ķ���ģʽ
start->   DS.
D->B; D
D->��
B->int L    { L.type := int }|real L    { L.type := real }|char L    { L.type := char }|bool L    { L.type := bool }
L->id   { A.Type := L.type  enter(v.entry,L.type)}  A
A-> ��idA   { A1.Type := A.type  enter(v.entry,A.type)}
A->��

S�� V := EC { gen( ":=", E.place,0,V.place) } H
H����S | ��
C-><E|>E|��
E->T    { R.i:=T.place}      R     {E.place:=R.s}
R->+T    { R1.i:= newtemp; gen( "*", R.i, T.place , R1.i) }     R   {R.s:= R1.s; }|-TR
R-> ��    {Rs=R.i}
T->FP
P->*FP|/FP|��
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

#define txmax 100    /* ���ű�������� */
#define al 10        /* ���ŵ���󳤶� */
#define tvmax 500    /* ����ܹ��������ʱ����ȡֵ��Χ[100, tvmax] */
#define norw 4       /* �ؼ��ָ��� */
#define cxmax 500   /* ��������������� */

int tx;              //���ֱ�ָ��, ȡֵ��Χ[0, txmax-1]
int tv ;             //��ʱ��������

/* ���� */
enum symbol {
    nul,         eeof,	ident,         plus,      times,	lparen,divide,sub,morethan,lessthan,
	rparen,    comma,     semicolon,  becomes,  period, realsym,    intsym,charsym,boolsym
};

enum symbol sym;    /* ��ǰ�ķ��� */
char ch;            /* ��ȡ�ַ��Ļ�������getch ʹ�� */
char id[al+1];      /* ��ǰident, �����һ���ֽ����ڴ��0 */
char a[al+1];       /* ��ʱ����, �����һ���ֽ����ڴ��0 */

/* ���ű�ṹ */
struct tablestruct
{
   char name[al];      /* ���� */
    enum symbol type;   // ����
};

struct tablestruct table[txmax]; /* ���ű� */

char word[norw][al];        /* ������ */
enum symbol wsym[norw];     /* �����ֶ�Ӧ�ķ���ֵ */
enum symbol ssym[256];      /* ���ַ��ķ���ֵ��ɢ�б� */
enum symbol tvtype[501];

int cx;             /* ��Ԫʽ����ָ��, ȡֵ��Χ[0, cxmax-1]*/
struct instruction
{
    char f[al+1]; /* ������ */
    char l[al+1];     /* ������� */
    char r[al+1];     /* �Ҳ�����*/
	char t[al+1];     /* ��� */
};
struct instruction code[cxmax]; /* ����������������� */

FILE* fin;
FILE* fout;

int getsym();
void enter(enum symbol type);
void init();
int position(char* idt);
int gen(enum symbol op, int arg1, int arg2,int result );     //�м�������
void writecode(char *op, char *arg1, char *arg2,char *result );    //д����
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

	printf("������������ļ���:");
	gets(filename);
	if((fin=fopen(filename,"r"))==NULL)
	{
		printf("���ܴ��ļ�.\n");
		exit(0);
	}

    init();                  //��ʼ��
    getsym();                //����һ�����ʣ�������������sym�У����ִ�ֵ����id��
	start();                //��ʼ��start->DS.  ����

    if (sym==eeof)
	{
		printf("�﷨��ȷ\n\n������м���뱣�浽�ļ��������ļ���������س�");
		gets(filename);
		if(strlen(filename)<=0) return 0;
		if((fout=fopen(filename,"w"))==NULL)
		{
			printf("���ܴ��ļ�.\n");
			exit(0);
		}
		for (int cx1=0;cx1<cx;cx1++)
			fprintf(fout,"(%s,%s,%s,%s)\n",code[cx1].f,code[cx1].l,code[cx1].r,code[cx1].t);
		return 0;
	}
	else {printf("�﷨��1:  . �������о���"); exit(0);}
	fclose(fin);
	fclose(fout);
}

//��ʼ������
void init()
{
	int i;

	/* ���õ��ַ����� */
	for (i=0; i<=255; i++)
	{
		ssym[i] = nul;            //����ȷ�ĵ��ַ�����Ϊnul����Ԥ�ó�ֵnul
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

	/* ���ñ��������� */
	strcpy(&(word[0][0]), "real");
	strcpy(&(word[1][0]), "int");
	strcpy(&(word[2][0]), "char");
	strcpy(&(word[3][0]), "bool");

	/* ���ñ����ַ��� */
	wsym[0] = realsym;
	wsym[1] = intsym;
	wsym[2] = charsym;
	wsym[3] = boolsym;

	tv=100;           //��ʱ����ָ���ֵ����Tx��tv��ȡֵû�н��������𵽵�����ʱ������������ı���
	tx=0;           //��ָ���ֵ
	cx=0;     //ָ�������

}

/*
* �ʷ���������ȡһ������
*/
int getsym()
{
	int i,k;
	ch=fgetc(fin);

	if (ch==EOF) {sym=eeof; return 0;}         //�ļ�����

	while (ch==' ' || ch==10 || ch==13 || ch==9)  /* ���Կո񡢻��С��س���TAB */
		ch=fgetc(fin);

	if (ch>='a' && ch<='z')
	{           /* ���ֻ�������a..z��ͷ ��*/
		k = 0;
		do
		{
			if(k<al)                  /* ���ŵ���󳤶�Ϊal �������ͽ�β����*/
			{
				a[k] = ch;
				k++;
			}
			ch=fgetc(fin);
		} while (ch>='a' && ch<='z' || ch>='0' && ch<='9');

		a[k] = 0;
		strcpy(id, a);
		fseek(fin,-1,1);

		for (i=0;i<norw;i++)        /* ������ǰ�����Ƿ�Ϊ������ */
			 if (strcmp(id,word[i]) == 0)
					 break;
		if (i <norw)
		{
			sym = wsym[i];
		}
		else
		{
			sym = ident;          /* ����ʧ���������Ǳ�ʶ�� */

		}
	}
	else if(ch == ':') /* ��⸳ֵ���� */
	{
		ch=fgetc(fin);
		if (ch == '=')
		{
			sym = becomes;
		}
		else
		{
			sym = nul;  /* ����ʶ��ķ��� */
		}
	}
	else sym = ssym[ch];     /* �����Ų�������������ʱ��ȫ�����յ��ַ����Ŵ��� */
	return 0;
}

/*
* �ڷ��ű��м���һ��
*/

void enter(enum symbol type)
{
	tx=tx+1;
	if (tx > txmax)
    {
		printf(" ���ű�Խ�� ");           /* ���ű�Խ�� */
		return;
	}
	int i = 0;
	for(i; i < tx; i++)
    {
        if(strcmp(table[i].name,id)==0)
        {
            printf("�����Ѿ��������������ظ�������\n");
            exit(0);
        }
	}
	strcpy(table[tx].name, id); /* ȫ�ֱ���id���Ѵ��е�ǰ���ֵ�����,TxΪ���뵱ǰ����֮ǰ��βָ�� */
	table[tx].type = type;

}

/*
* �������ֵ�λ��.
* �ҵ��򷵻������ֱ��е�λ��,���򷵻�0.
*
* idt:    Ҫ���ҵ�����
* tx:     ��ǰ���ֱ�βָ�룬ȫ�ֱ���
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

/* �м����*/
int gen(enum symbol op, int arg1, int arg2,int result )
{
	char temp1[al+1],temp2[al+1],temp3[al+1];
	if(arg1>=100)                            //ģ��������ʱ����
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
	if(op==becomes)//����ƥ����
    {
        if(arg1<=100)
        {
            if(table[arg1].type!=table[result].type)
            {
                printf("��ֵ�����Ҳ��������Ͳ�ƥ��!");exit(0);
            }
        }
        else if(arg1>100&&arg1<=501)
        {
            if(tvtype[arg1]!=table[result].type)
            {
                printf("��ֵ�����Ҳ��������Ͳ�ƥ��!");exit(0);
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
                    printf("%d�����Ҳ��������Ͳ�ƥ��!",op);exit(0);
                }
            }
            else if(arg2>100&&arg2<=501)
            {
                if(table[arg1].type!=tvtype[arg2])
                {
                    printf("%d�����Ҳ��������Ͳ�ƥ��!",op);exit(0);
                }
            }
        }
        else if(arg1>100&&arg1<=501)
        {
            if(arg2<=100)
            {
                if(tvtype[arg1]!=table[arg2].type)
                {
                    printf("%d�����Ҳ��������Ͳ�ƥ��!",op);exit(0);
                }
            }
            else if(arg2>100&&arg2<=501)
            {
                if(tvtype[arg1]!=tvtype[arg2])
                {
                    printf("%d�����Ҳ��������Ͳ�ƥ��!",op);exit(0);
                }
            }
        }
    }
    if(op==becomes)
    {
        if(result<=100)
        {
            if(table[result].type==charsym) {printf("char���ͱ������ܽ��и�ֵ����!");exit(0);}
        }
        else {printf("��ֵ����߲����������ı���.");exit(0);}
    }
	if (op==becomes)
	{
		printf("(:=,%s,%s,%s)\n",temp1,temp2,temp3);
		writecode(":=",temp1,temp2,temp3);
	}
	else if (op==plus)                          //+����
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

//��������
void writecode(char op[al+1], char arg1[al+1], char arg2[al+1],char result[al+1] )
{
	if (cx >= cxmax)
	{
		printf("Program too long"); /* ������� */
		return ;
	}
	strcpy(code[cx].f, op);
	strcpy(code[cx].l,arg1);
	strcpy(code[cx].r,arg2);
	strcpy(code[cx].t,result);
	cx++;
	return ;
}

/*��������ʽ     P->DS.   */

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
		{printf("�﷨��2�� ȱ�ٳ������."); exit(0);}
	}
	else
	{printf("�﷨��3: ����ֻ����int,real,bool,��char��ʼ���������ִ�Сд"); exit(0);}
}

/*�ݹ��½�����
D->  B; D
D->��
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
		{printf("�﷨��4:ȱ��;"); exit(0);}
	}
	else if(sym==ident || sym==period)  return;

	else {printf("�﷨��5"); exit(0);}
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
	{printf("�﷨��6:����ֻ����int,real,bool,char����"); exit(0);}
}

/*
L->   id   { A.Type := L.type  enter(v.entry,L.type)}   A       V.entryͨ��ȫ�ֱ���tx���Դ���
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
	{printf("�﷨��7:������������"); exit(0);}
}

/*
A-> ��id  A   { A1.Type := A.type  enter(v.entry,A.type)}
A->��
*/

void A(enum symbol type)
{
	if (sym==comma)          //��ǰ����Ϊ��
	{
		getsym();
		if (sym==ident)
		{
			enter(type);
			getsym();
			A(type);
		}
		else
		{printf("�﷨��8:һ������������������б����ı�����������"); exit(0);}
	}
	else if (sym== semicolon)   return ;//��ǰ����Ϊ����A��follow��Ԫ�أ��൱�ڽ���A->��
	else
	{printf("�﷨��9"); exit(0);}
}

/*
S�� V := EC { gen( ":=", E.place,0,V.place) } H
*/
void S()
{
	int vplace,Eplace,Cplace;
	if (sym==ident)
	{
		vplace=V();
		//getsym();
		if (sym==becomes)     //��ǰ����Ϊ:=
		{
			getsym();
			Eplace=E();
			Cplace=C(Eplace);
            gen(becomes,Cplace,-1,vplace);
            H();
		}
		else
		{printf("�﷨��10:ȱ��:="); exit(0);}
	}
	else {printf("�﷨��11"); exit(0);}
}

/*
H����S | ��
*/
void H()
{
	if (sym==semicolon)          //��ǰ����Ϊindent����
	{
		getsym();
		S();
	}
	else if (sym==period)   return ;
	else
	{printf("�﷨��12"); exit(0);}
}

/*
C-<E|>E|��
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
            if(table[Eplace].type==boolsym) {printf("bool����ֵ���ܽ��й�ϵ����<��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��й�ϵ����<��");exit(0);}
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
            if(table[Eplace].type==boolsym) {printf("bool����ֵ���ܽ��й�ϵ����>��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��й�ϵ����>��");exit(0);}
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
    else {printf("�﷨��13");exit(0);}
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
		{printf("�﷨��14"); exit(0);}
	return Rs;
}

/*
R->+T    { R1.i:= newtemp; gen( "*", R.i, T.place , R1.i) }     R   {R.s:= R1.s; }|-TR
R-> ��    {R.s=R.i}
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
            if(table[tplace].type==charsym) {printf("char����ֵ���ܽ��д�������+��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char����ֵ���ܽ��д�������+��");exit(0);}
        }
		if(tplace<=100)
        {
            if(table[tplace].type==boolsym) {printf("bool����ֵ���ܽ��д�������+��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��д�������+��");exit(0);}
        }
        tv=tv+1;            //������ʱ����
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
            if(table[tplace].type==charsym) {printf("char����ֵ���ܽ��д�������-��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char����ֵ���ܽ��д�������-��");exit(0);}
        }
		if(tplace<=100)
        {
            if(table[tplace].type==boolsym) {printf("bool����ֵ���ܽ��д�������-��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��д�������-��");exit(0);}
        }
        tv=tv+1;            //������ʱ����
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
	else {printf("�﷨��15"); exit(0);}
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
        {printf("�﷨��16"); exit(0);}
	return Ps;
}

/*
P->*FP|/FP|��
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
            if(table[fplace].type==charsym) {printf("char����ֵ���ܽ��д�������*��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char����ֵ���ܽ��д�������*��");exit(0);}
        }
		if(fplace<=100)
        {
            if(table[fplace].type==boolsym) {printf("bool����ֵ���ܽ��д�������*��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��д�������*��");exit(0);}
        }
        tv=tv+1;            //������ʱ����
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
            if(table[fplace].type==charsym) {printf("char����ֵ���ܽ��д�������/��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==charsym) {printf("char����ֵ���ܽ��д�������/��");exit(0);}
        }
		if(fplace<=100)
        {
            if(table[fplace].type==boolsym) {printf("bool����ֵ���ܽ��д�������/��");exit(0);}
        }
        else
        {
            if(tvtype[tv]==boolsym) {printf("bool����ֵ���ܽ��д�������/��");exit(0);}
        }
        tv=tv+1;            //������ʱ����
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
	else {printf("�﷨��17"); exit(0);}
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
		if (Fplace==0)  {printf("����û������"); exit(0);}
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
			printf("�﷨��ȱ)"); exit(0);
		}
	}
	else{printf("�﷨��,ȱ("); exit(0);}
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
		if (Vplace==0)  {printf("����û������"); exit(0);}
		getsym();
	}
	else{printf("�﷨��18"); exit(0);}
	return Vplace;
}
