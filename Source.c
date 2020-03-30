#include <signal.h>
#include <setjmp.h>
#include<stdio.h>
#include<stdlib.h>
const int BLSIZE = 4096;  const int NBLK = 2047;  const int FNSIZE = 128;  const int LBSIZE = 4096;
const int ESIZE = 256; const int GBSIZE = 256;  const int NBRA = 5;  const int KSIZE = 9;  const int CBRA = 1;
const int CCHR = 2;  const int CDOT = 4;  const int CCL = 6;  const int NCCL = 8;  const int CDOL = 10;
const int CEOF = 11;  const int CKET = 12;  const int CBACK = 14;  const int CCIRC = 15;  const int STAR = 01;
const int READ = 0;  const int WRITE = 1;
int	peekc, given, lastc, ninbuf, io, pflag, vflag = 1, oflag, listf, listn, col, tfile = -1, tline, iblock = -1, oblock = -1;
int ichanged, nleft, names[26], anymarks, nbra, subnewa, subolda, fchange, wrapp, bpagBUFSIZ = 20;
char savedfile[128], file[128], linebuf[4096], rhsbuf[4096 / 2], expbuf[BUFSIZ + 4], genbuf[4096], * nextip ;
char WRERR[] = "WRITE ERROR", * braslist[5], * braelist[5], tmpXXXXX[50] = "/tmp/eXXXXX", * globp, * linebp;
char line[70], * linp = line, T[] = "TMP", Q[] = "", * tfname, * loc1, * loc2, ibuff[4096], obuff[4096], grepbuf[256];
unsigned int* addr1, * addr2, * dot, * dol, * zero, nlall = 128;
long count;
long lseek(int, long, int);int	open(char*, int);int creat(char*, int);int	read(int, char*, int);
int	write(int, char*, int);int	close(int);int	fork(void);int	execl(char*, ...);int	wait(int*);
char* mktemp(char*);char* getblock(unsigned int atl, int iof);char* getline(unsigned int tl);
char* place(char* sp, char* l1, char* l2);void add(int i);int advance(char* lp, char* ep);
int append(int (*f)(void), unsigned int* a);int backref(int i, char* lp);void blkio(int b, char* buf, int (*iofcn)(int, char*, int));
/*void callunix(void)*/;int cclass(char* set, int c, int af);void commands(void);void compile(int eof);
int compsub(void);void dosub(void);void error(char* s);int execute(unsigned int* addr);
void exfile(void);void filename(int comm);void gdelete(void);int getcopy(void);int getfile(void);
int getnum(void);int getsub(void);int gettty(void);int gety(void);void global(int k);
void init(void);unsigned int* address(void);void join(void);void move(int cflag);void newline(void);
void nonzero(void);void onhup(int n);void onintr(int n);void print(void);void putd(void);
void putfile(void);int putline(void);void quit(int n);void rdelete(unsigned int* ad1, unsigned int* ad2);
void reverse(unsigned int* a1, unsigned int* a2);void setwide(void);void setnoaddr(void);
void squeeze(int i); void substitute(int inglob); void greperror(char c); void readfile(const char* c);
void search(const char* c); void search_file(const char* filename, const char* searchfor);
jmp_buf	savej;
typedef void (*SIG_TYP)(int);
SIG_TYP	oldhup, oldquit;
#define	SIGHUP	1	/* hangup */
#define	SIGQUIT	3	/* quit (ASCII FS) */
int main(int argc, char* argv[]) { char* p1, * p2; SIG_TYP oldintr; oldquit = signal(SIGQUIT, SIG_IGN);
	oldhup = signal(SIGHUP, SIG_IGN); oldintr = signal(SIGINT, SIG_IGN);
	if (signal(SIGTERM, SIG_IGN) == SIG_DFL) signal(SIGTERM, quit);	argv++;
	while (argc > CBRA && **argv == '-') {switch ((*argv)[1]) {
		case '\0':	vflag = 0;	break;
		case 'q':   signal(SIGQUIT, SIG_DFL);	vflag = 1;	break;
		case 'o':	oflag = 1;	break;}
		argv++; argc--; }
	if (oflag) {p1 = "/dev/stdout"; p2 = savedfile; while (*p2++ = *p1++) {} }
	if (argc > 1) { p1 = *argv;  p2 = savedfile;
		while ((*p2++ = *p1++) == CBRA) { if (p2 >= &savedfile[sizeof(savedfile)]) { p2--; } }  globp = "r";
	}
	zero = (unsigned*)malloc(nlall * sizeof(unsigned));	tfname = mktemp(tmpXXXXX);	init();
	if (oldintr != SIG_IGN) signal(SIGINT, onintr);	if (oldhup != SIG_IGN) signal(SIGHUP, onhup);
	setjmp(savej); commands(); search_file(* filename,*argv[2]); quit(0); return 0;
}
void commands(void) {unsigned int* a1; int c, temp; char lastsep;
	for (;;) {if (pflag) { pflag = 0;	addr1 = addr2 = dot;	print();	}
		c = '\n';
		for (addr1 = 0;;) {	
			lastsep = c;	a1 = address();	c = getchar();
			if (c != ',' && c != ';')	break;
			if (lastsep == ',')	error(Q);
			if (a1 == 0) {	a1 = zero + 1;
				if (a1 > dol)	a1--;	}
			addr1 = a1;
			if (c == ';')	dot = a1;	}
		if (lastsep != '\n' && a1 == 0)	a1 = dol;
		if ((addr2 = a1) == 0) {	given = 0;	addr2 = dot;	}
		else	given = 1;
		if (addr1 == 0)	addr1 = addr2;
		switch (c) {
		case '\n':	if (a1 == 0) { a1 = dot + CBRA; addr2 = a1; addr1 = a1; }	if (lastsep == ';') { addr1 = a1; }	print();	continue;
		case 'e':	setnoaddr();
			if (vflag && fchange) { fchange = 0;	error(Q); }
			filename(c); init();	addr2 = zero;	goto caseread;
		case 'g':	global(CBRA);	continue;
		case 'p':	case 'P':	newline();	print();	continue;
		case 'Q':	fchange = 0;	case 'q':	setnoaddr();	newline();	quit(0);
		case 'W':	wrapp++; case 'w':	setwide();	squeeze(dol > zero);
			if ((temp = getchar()) != 'q' && temp != 'Q') { peekc = temp;	temp = 0; }	filename(c);
			if (!wrapp || ((io = open(file, CBRA)) == -1) || ((lseek(io, 0L, 2)) == -1))
				if ((io = creat(file, 0666)) < 0) { error(file); }	wrapp = 0;
			if (dol > zero)	putfile(); {exfile(); }	if (addr1 <= zero + CBRA && addr2 == dol) { fchange = 0; }
			if (temp == 'Q') { fchange = 0; }	if (temp) { quit(0); }	continue;
		caseread:
			if ((io = open(file, 0)) < 0) { lastc = '\n';	error(file); }	setwide();	squeeze(0);
			ninbuf = 0;	c = zero != dol;	append(getfile, addr2);	exfile();	fchange = c;	continue;
		case 'a'://	add(0);	continue;
		case 'c'://	nonzero();	newline();	rdelete(addr1, addr2);	append(gettty, addr1 - 1);	continue;
		case 'd'://	nonzero();	newline();	rdelete(addr1, addr2);	continue;
		case 'E'://	fchange = 0;	c = 'e';		
		case 'f'://	setnoaddr();	filename(c);	puts(savedfile);	continue;		
		case 'i'://	add(-1);	continue;
		case 'j'://	if (!given) { addr2++; }	newline();	join();	continue;
		case 'k'://	nonzero();
			//if ((c = getchar()) < 'a' || c > 'z') { error(Q); }	newline();	names[c - 'a'] = *addr2 & ~01;	anymarks |= 01;	continue;
		case 'm'://	move(0);	continue;
		case 'n'://	listn++;	newline();	print();	continue;
		case 'l'://	listf++;
		case 'r'://	filename(c);
		case 's'://	nonzero();	substitute(globp != 0);	continue;
		case 't'://	move(CBRA);	continue;
		case 'u'://	nonzero();	newline();	if ((*addr2 & ~01) != subnewa) { error(Q); }	*addr2 = subolda;
		//	dot = addr2;	continue;
		case 'v'://	global(0);	continue;
		case '='://	setwide();	squeeze(0);	newline();	count = addr2 - zero;	putd();	putchar('\n');	continue;
		case '!'://	callunix();	continue;
		case EOF:	return;
		default: caseGrepError:  greperror(c);  continue;
		}	error(Q);	} }
void greperror(char c) {
	getchar();  /* throw away '\n' */
	snprintf(grepbuf, sizeof(grepbuf), "\'%c\' is a non-grep command", c);  puts(grepbuf);
}
void print(void) {	unsigned int* a1;	nonzero();	a1 = addr1;
	do {	if (listn) {	count = a1 - zero;	putd();	putchar('\t');	}	puts(getline(*a1++));}
	while (a1 <= addr2); {dot = addr2; }
	listf = 0;	listn = 0;	pflag = 0;}
unsigned int*address(void) {
	int sign = 1, opcnt = 0, nextopand = -1, c;
	unsigned int* a = dot, * b;
	do {	do c = getchar(); while (c == ' ' || c == '\t');
	if ('0' <= c && c <= '9') { peekc = c;	if (!opcnt) { a = zero; }	a += sign * getnum(); }
		else switch (c) {
		case '$':	a = dol;
		case '.':	if (opcnt) { error(Q); }	break;
		case '\'':	c = getchar();	if (opcnt || c < 'a' || 'z' < c) { error(Q); }	a = zero;
			do a++; while (a <= dol && names[c - 'a'] != (*a & ~01));	break;
		case '?':	sign = -sign;
		case '/':	compile(c);	b = a;
			for (;;) {	a += sign;
			if (a <= zero) { a = dol; }
			if (a > dol) { a = zero; }
			if (execute(a)) { break; }
			if (a == b) { error(Q); }	}
			break;
		default:
			if (nextopand == opcnt) {	a += sign;	if (a < zero || dol < a) { continue; }  }
			if (c != '+' && c != '-' && c != '^') {	peekc = c;	if (opcnt == 0) { a = 0; }	return (a);	}	sign = CBRA;
			if (c != '+')	sign = -sign;	nextopand = ++opcnt;	continue;	}
		sign = CBRA;	opcnt++; } 
	while (zero <= a && a <= dol);	error(Q);	return 0; }
int getnum(void) {	int r = 0, c;	while ((c = getchar()) >= '0' && c <= '9') { r = r * 10 + c - '0'; }	peekc = c;	return (r); }
void setwide(void) {	if (!given) {	addr1 = zero + (dol > zero);	addr2 = dol;	}	}
void setnoaddr(void) {	if (given)	error(Q);}
void nonzero(void) {	squeeze(CBRA);	}
void squeeze(int i) {if (addr1<zero + i || addr2>dol || addr1 > addr2)	error(Q);	}
void newline(void) {
	int c;
	if ((c = getchar()) == '\n' || c == EOF)	return;
	if (c == 'p' || c == 'l' || c == 'n') {	pflag++;
		if (c == 'l')	listf++;	else if (c == 'n')	listn++;
		if ((c = getchar()) == '\n')	return; }
	error(Q); }
void filename(int comm) { char* p1, * p2; int c = getchar(); count = 0;
	if (c == '\n' || c == EOF) {	p1 = savedfile;
	if (*p1 == 0 && comm != 'f') { error(Q); }	p2 = file;
	while (*p2++ = *p1++) {}	return; }
	if (c != ' ')	error(Q);
	while ((c = getchar()) == ' ') {}
	if (c == '\n')	error(Q);
	p1 = file;
	do { if (p1 >= &file[sizeof(file) - CBRA] || c == ' ' || c == EOF) { error(Q); } *p1++ = c; }
	while ((c = getchar()) != '\n');
	*p1++ = 0;
	if (savedfile[0] == 0 || comm == 'e' || comm == 'f') {	p1 = savedfile;	p2 = file;	while (*p1++ = *p2++) {}	}	}
void exfile(void) {close(io);io = -1;	if (vflag) {	putd();	putchar('\n');	}}
void onintr(int n) {	signal(SIGINT, onintr);	putchar('\n');	lastc = '\n';	error(Q);}
void onhup(int n) {	signal(SIGINT, SIG_IGN);  signal(SIGHUP, SIG_IGN);
	if (dol > zero) { addr1 = zero + 1;  addr2 = dol;  io = creat("ed.hup", 0600);  if (io > 0) { putfile(); } }
	fchange = 0;  quit(0); }
void error(char* s) {	int c;	wrapp = 0;	listf = 0;	listn = 0;
putchar('?');	puts(s);	count = 0;	lseek(0, (long)0, 2);	pflag = 0;
	if (globp) { lastc = '\n'; }	globp = 0;	peekc = lastc;
	if (lastc)	while ((c = getchar()) != '\n' && c != EOF) {}
	if (io > 0) {	close(io);	io = -1;	}	longjmp(savej, CBRA);	}
int gettty(void) {	int rc;
	if (rc = gety())	return(rc);
	if (linebuf[0] == '.' && linebuf[CBRA] == 0)	return(EOF);
	return(0);	}
int gety(void) {	int c;	char* gf = globp, * p = linebuf;
	while ((c = getchar()) != '\n') {
		if (c == EOF) { if (gf) { peekc = c; }	return(c); }
		if ((c &= 0177) == 0)	continue;	*p++ = c;
		if (p >= &linebuf[4096 - 2])	error(Q);	}	*p++ = 0;	return(0);}
int getfile(void) {	int c;	char* lp = linebuf, * fp = nextip;
	do {	if (--ninbuf < 0) {	if ((ninbuf = read(io, genbuf, 4096) - 1) < 0)
				if (lp > linebuf) {	puts("'\\n' appended");	*genbuf = '\n';	}
				else return(EOF);	fp = genbuf;
			while (fp < &genbuf[ninbuf]) {	if (*fp++ & 0200)	break;	}	fp = genbuf;	}
		c = *fp++;
		if (c == '\0')	continue;
		if (c & 0200 || lp >= &linebuf[4096]) { lastc = '\n';	error(Q); }
		*lp++ = c;	count++;
	} while (c != '\n');	*--lp = 0;	nextip = fp;	return(0);}
void putfile(void) { unsigned int* a1;  char* fp, * lp;  int n, nib = 4096;  fp = genbuf;  a1 = addr1;
	do {	lp = getline(*a1++);
		for (;;) {	if (--nib < 0) {	n = (int)(fp - genbuf);
				if (write(io, genbuf, n) != n) { puts(WRERR);  error(Q); }  nib = 4096 - 1;  fp = genbuf; }
			count++;  if ((*fp++ = *lp++) == 0) { fp[-1] = '\n';  break; }	}
	} while (a1 <= addr2);
	n = (int)(fp - genbuf);  if (write(io, genbuf, n) != n) { puts(WRERR);  error(Q); } }
int append(int (*f)(void), unsigned int* a) { unsigned int* a1, * a2, * rdot; int nline = 0, tl;	dot = a;
	while ((*f)() == 0) {	if ((dol - zero) + 1 >= nlall) {	unsigned* ozero = zero;	nlall += 1024;
			if ((zero = (unsigned*)realloc((char*)zero, nlall * sizeof(unsigned))) == NULL) {	error("MEM?");	onhup(0);	}
			dot += zero - ozero;	dol += zero - ozero;	}
		tl = putline();	nline++;	a1 = ++dol;	a2 = a1 + 1;	rdot = ++dot;
		while (a1 > rdot) { *--a2 = *--a1; }	*rdot = tl;	}	return(nline);	}
void add(int i) {	if (i && (given || dol > zero)) {	addr1--;	addr2--;	}
	squeeze(0);	newline();	append(gettty, addr2);	}
/*void callunix(void) {	SIG_TYP savint;	int pid, rpid, retcode;	setnoaddr();
	if ((pid = fork()) == 0) {	signal(SIGHUP, oldhup);	signal(SIGQUIT, oldquit);	execl("/bin/sh", "sh", "-t", 0);	exit(0100);	}
	savint = signal(SIGINT, SIG_IGN);
	while ((rpid = wait(&retcode)) != pid && rpid != -1);	signal(SIGINT, savint);
	if (vflag) {	puts("!");	}	}*/
void quit(int n) {	if (vflag && fchange && dol != zero) {	fchange = 0;error(Q);}	_unlink(tfname);exit(0);}
void rdelete(unsigned int* ad1, unsigned int* ad2) {
	unsigned int* a1 = ad1, * a2 = ad2 + 1, * a3 = dol;	dol -= a2 - a1;
	do {*a1++ = *a2++;	}	while (a2 <= a3);	a1 = ad1;
	if (a1 > dol)	a1 = dol;	dot = a1;	fchange = CBRA;}
void gdelete(void) {	unsigned int* a1, * a2, * a3 = dol;
	for (a1 = zero; (*a1 & 01) == 0; a1++)	if (a1 >= a3)		return;
	for (a2 = a1 + CBRA; a2 <= a3;) {	if (*a2 & 01) {	a2++;	dot = a1;}
		else	*a1++ = *a2++;}	dol = a1 - 1;
	if (dot > dol)	dot = dol;	fchange = 1;}
char* getline(unsigned int tl) {	char* bp = getblock(tl &= ~((4096 / 2) - CBRA), READ), * lp = linebuf;	int nl = nleft;
	while (*lp++ = *bp++)	if (--nl == 0) {bp = getblock(tl += (4096 / 2), READ);	nl = nleft;	}
	return(linebuf);}
int putline(void) {	unsigned int tl = tline;char* bp = getblock(tl &= ~((4096 / 2) - CBRA), WRITE), * lp = linebuf;
	int nl = nleft;	fchange = CBRA;
	while (*bp = *lp++) {	if (*bp++ == '\n') {*--bp = 0;	linebp = lp;	break;	}
		if (--nl == 0) {	bp = getblock(tl += (4096 / 2), WRITE);	nl = nleft;	}	}
	nl = tline;	tline += (((lp - linebuf) + 03) >> CBRA) & 077776;	return(nl);}
char*getblock(unsigned int atl, int iof) {	int bno = (atl / (4096 / 2)), off = (atl << CBRA) & (4096 - CBRA) & ~03;
	if (bno >= NBLK) {	lastc = '\n';	error(T);}	nleft = 4096 - off;
	if (bno == iblock) {	ichanged |= iof;	return(ibuff + off);}
	if (bno == oblock)	return(obuff + off);
	if (iof == READ) {
	if (ichanged) { blkio(iblock, ibuff, write); } ichanged = 0; iblock = bno;	blkio(bno, ibuff, read); return(ibuff + off);	}
	if (oblock >= 0) { blkio(oblock, obuff, write); }	oblock = bno;	return(obuff + off);}
void blkio(int b, char* buf, int (*iofcn)(int, char*, int)) {	lseek(tfile, (long)b * 4096, 0);
	if ((*iofcn)(tfile, buf, 4096) != 4096) {	error(T);}}
void init(void) {	int* markp;	close(tfile);	tline = 2;
	for (markp = names; markp < &names[26]; )	*markp++ = 0;	subnewa = 0;	anymarks = 0;	iblock = -1;	oblock = -1;	ichanged = 0;
	close(creat(tfname, 0600));	tfile = open(tfname, 2);	dot = dol = zero;}
void global(int k) {	char globuf[BUFSIZ],* gp = globuf ;	int c;	unsigned int* a1;
	if (globp)	error(Q);	setwide();	squeeze(dol > zero);
	if ((c = getchar()) == '\n')	error(Q);	compile(c);
	while ((c = getchar()) != '\n') {	if (c == EOF) { error(Q); }
		if (c == '\\') {	c = getchar();	if (c != '\n')	*gp++ = '\\';	}	*gp++ = c;
		if (gp >= &globuf[BUFSIZ - 2])	error(Q);	}
	if (gp == globuf)	*gp++ = 'p';	*gp++ = '\n';	*gp++ = 0;
	for (a1 = zero; a1 <= dol; a1++) {	*a1 &= ~01;	if (a1 >= addr1 && a1 <= addr2 && execute(a1) == k)	*a1 |= 01;	}
	if (globuf[0] == 'd' && globuf[CBRA] == '\n' && globuf[2] == '\0') {	gdelete();	return;	}
	for (a1 = zero; a1 <= dol; a1++) {	if (*a1 & 01) {	*a1 &= ~01;	dot = a1;	globp = globuf;	commands();	a1 = zero;	}	}}
void join(void) {	char* gp = genbuf, * lp;	unsigned int* a1;	nonzero();
	for (a1 = addr1; a1 <= addr2; a1++) {	lp = getline(*a1);
		while (*gp = *lp++)	if (gp++ >= &genbuf[4096 - 2])	error(Q);	}	lp = linebuf;	gp = genbuf;
	while (*lp++ = *gp++);	*addr1 = putline();
	if (addr1 < addr2)	rdelete(addr1 + CBRA, addr2);	dot = addr1;}
void substitute(int inglob) {	int* mp, nl; unsigned int* a1; int gsubf = compsub(); int n = getnum();
	for (a1 = addr1; a1 <= addr2; a1++) {	if (execute(a1)) {	unsigned* ozero;	int m = n;
	do {int span = loc2 - loc1;	if (--m <= 0) {	dosub();
	if (!gsubf)	break;	if (span == 0) {	if (*loc2 == '\0')	break;	loc2++;	}	}
	} while (execute((unsigned*)0));	if (m <= 0) {	inglob |= 01;	subnewa = putline();	*a1 &= ~01;
	if (anymarks) {	for (mp = names; mp < &names[26]; mp++)	if (*mp == *a1)	*mp = subnewa;	}
	subolda = *a1;	*a1 = subnewa;	ozero = zero;	nl = append(getsub, a1);	nl += zero - ozero;	a1 += nl;	addr2 += nl;	}	}}
	if (inglob == 0)	error(Q);}
int compsub(void) {	int seof, c;	char* p;
	if ((seof = getchar()) == '\n' || seof == ' ')	error(Q);	compile(seof);	p = rhsbuf;
	for (;;) {	c = getchar();
		if (c == '\\')	c = getchar() | 0200;
		if (c == '\n') {	if (globp && globp[0])	c |= 0200;
			else {	peekc = c;	pflag++;	break;	}	}
		if (c == seof)	break;	*p++ = c;
		if (p >= &rhsbuf[4096 / 2])	error(Q);	}	*p++ = 0;
	if ((peekc = getchar()) == 'g') {	peekc = 0;	newline();	return(1);	}	newline();	return(0);}
int getsub(void) {	char* p1, * p2;	p1 = linebuf;
	if ((p2 = linebp) == 0)	return(EOF); while (*p1++ = *p2++);	linebp = 0;	return(0); }
void dosub(void) {	char* lp, * sp, * rp;	int c;	lp = linebuf; sp = genbuf;	rp = rhsbuf;
	while (lp < loc1)	*sp++ = *lp++;
	while (c = *rp++ & 0377) {	if (c == '&') {	sp = place(sp, loc1, loc2);	continue;	}
		else if (c & 0200 && (c &= 0177) >= '1' && c < nbra + '1') {
	sp = place(sp, braslist[c - '1'], braelist[c - '1']); continue; }	*sp++ = c & 0177;
		if (sp >= &genbuf[4096])	error(Q);	}
	lp = loc2;	loc2 = sp - genbuf + linebuf;
	while (*sp++ = *lp++) {	if (sp >= &genbuf[4096]) { error(Q); } }
	lp = linebuf;	sp = genbuf;	while (*lp++ = *sp++)	; }
char* place(char* sp, char* l1, char* l2) {	while (l1 < l2) {	*sp++ = *l1++;
		if (sp >= &genbuf[4096])	error(Q);	}	return(sp); }
void move(int cflag) { unsigned int* adt, * ad1, * ad2; nonzero();
	if ((adt = address()) == 0)	error(Q);	newline();
	if (cflag) {unsigned int* ozero; int delta;	ad1 = dol;	ozero = zero; append(getcopy, ad1++);
		ad2 = dol;	delta = zero - ozero;	ad1 += delta;	adt += delta;	}
	else {	ad2 = addr2; for (ad1 = addr1; ad1 <= ad2;)	*ad1++ &= ~01;	ad1 = addr1; }	ad2++;
	if (adt < ad1) {	dot = adt + (ad2 - ad1); if ((++adt) == ad1) { return; }
		reverse(adt, ad1);	reverse(ad1, ad2);	reverse(adt, ad2);	}
	else if (adt >= ad2) {	dot = adt++;	reverse(ad1, ad2);	reverse(ad2, adt);	reverse(ad1, adt);	}
	else { error(Q); }	fchange = 1;}
void reverse(unsigned int* a1, unsigned int* a2) {	int t;
for (;;) {	t = *--a2;	if (a2 <= a1) { return; }	*a2 = *a1;	*a1++ = t;	} }
int getcopy(void) { if (addr1 > addr2) { return(EOF); }	getline(*addr1++);	return(0); }
void compile(int eof) {	int c, cclcnt;	char* ep, * lastep, bracket[5], * bracketp;	ep = expbuf; bracketp = bracket;
	if ((c = getchar()) == '\n') {	peekc = c;	c = eof;	}
	if (c == eof) {	if (*ep == 0) { error(Q); }	return;	}	nbra = 0;
	if (c == '^') {	c = getchar();	*ep++ = 15;	}	peekc = c;	lastep = 0;
	for (;;) {
	if (ep >= &expbuf[BUFSIZ])	{goto cerror;}	c = getchar();
	if (c == '\n') { peekc = c;	c = eof;	}
	if (c == eof) {	if (bracketp != bracket) { goto cerror; }	*ep++ = 11;	return;	}
	if (c != '*')	lastep = ep;
	switch (c) {
	case '\\':
		if ((c = getchar()) == '(') {
			if (nbra >= 5) { goto cerror; }	*bracketp++ = nbra;	*ep++ = CBRA;	*ep++ = nbra++;	continue;	}
	if (c == ')') {	if (bracketp <= bracket) { goto cerror; }	*ep++ = 12;	*ep++ = *--bracketp; continue;	}
		if (c >= '1' && c < '1' + NBRA) {	*ep++ = 14;	*ep++ = c - '1';	continue;	} *ep++ = 2;
		if (c == '\n') { goto cerror; }	*ep++ = c;	continue;
		case '.':	*ep++ = 4;	continue;
		case '\n':	goto cerror;
		case '*': if (lastep == 0 || *lastep == 1 || *lastep == 12) { goto defchar; } *lastep |= STAR; continue;
		case '$':	if ((peekc = getchar()) != eof && peekc != '\n') goto defchar;	*ep++ = 10;	continue;
		case '[':	*ep++ = 6;	*ep++ = 0;	cclcnt = 1;
			if ((c = getchar()) == '^') {	c = getchar();	ep[-2] = 8;}
			do {
			if (c == '\n')	goto cerror;
			if (c == '-' && ep[-1] != 0) {	if ((c = getchar()) == ']') { *ep++ = '-'; cclcnt++; break;	}
			while (ep[-1] < c) {
				*ep = ep[-1] + 1; ep++; cclcnt++; if (ep >= &expbuf[BUFSIZ]) { goto cerror; }	}	}
				*ep++ = c;	cclcnt++;
				if (ep >= &expbuf[BUFSIZ])	goto cerror;
			} while ((c = getchar()) != ']');	lastep[CBRA] = cclcnt;	continue;
	defchar: default: *ep++ = 2;	*ep++ = c;	}	} cerror:	expbuf[0] = 0;	nbra = 0;	error(Q); }
int execute(unsigned int* addr) {char* p1, * p2;	int c;
	for (c = 0; c < NBRA; c++) {	braslist[c] = 0;	braelist[c] = 0;	}	p2 = expbuf;
	if (addr == (unsigned*)0) {	if (*p2 == 15)	return(0);	p1 = loc2;	}
	else if (addr == zero)	return(0);
	else	p1 = getline(*addr);
	if (*p2 == 15) {	loc1 = p1;	return(advance(p1, p2 + 1));	}
	if (*p2 == 2) {	c = p2[1];
		do {	if (*p1 != c)	continue;
			if (advance(p1, p2)) {	loc1 = p1;	return(1);	}	} while (*p1++); return(0);	}
	do {	if (advance(p1, p2)) {	loc1 = p1;	return(1);	}	} while (*p1++); return(0); }
int advance(char* lp, char* ep) {	char* curlp;	int i;
for (;;) {
	switch (*ep++) {
	case 2:  if (*ep++ == *lp++) { continue; } return(0);
	case 4:  if (*lp++) { continue; }    return(0);
	case 10:  if (*lp == 0) { continue; }  return(0);
	case 11:  loc2 = lp;  return(1);
	case 6:   if (cclass(ep, *lp++, 1)) { ep += *ep;  continue; }  return(0);
	case 8:  if (cclass(ep, *lp++, 0)) { ep += *ep;  continue; }  return(0);
	case 1:  braslist[*ep++] = lp;  continue;
	case 12:  braelist[*ep++] = lp;  continue;
	case 14:
		if (braelist[i = *ep++] == 0) { error(Q); }
		if (backref(i, lp)) { lp += braelist[i] - braslist[i];  continue; }  return(0);
	case 14 | 01:
		if (braelist[i = *ep++] == 0) { error(Q); }  curlp = lp;
		while (backref(i, lp)) { lp += braelist[i] - braslist[i]; }
		while (lp >= curlp) { if (advance(lp, ep)) { return(1); }  lp -= braelist[i] - braslist[i]; }  continue;
	case 4 | 01:  curlp = lp;  while (*lp++) {}                goto star;
	case 2 | 01:  curlp = lp;  while (*lp++ == *ep) {}  ++ep;  goto star;
	case 6 | 01:
	case 8 | 01:  curlp = lp;  while (cclass(ep, *lp++, ep[-1] == (CCL | STAR))) {}  ep += *ep;  goto star;
	star:  do { lp--;  if (advance(lp, ep)) { return(1); } } while (lp > curlp);  return(0);
	default: error(Q);}}}
int backref(int i, char* lp) {	char* bp;	bp = braslist[i];
	while (*bp++ == *lp++)	if (bp >= braelist[i])	return(1);	return(0); }
int cclass(char* set, int c, int af) {	int n;
	if (c == 0)	return(0);	n = *set++;
	while (--n)	if (*set++ == c) return(af); return(!af); }
void putd(void) {	int r;	r = count % 10;	count /= 10;
	if (count)	putd();	putchar(r + '0'); }
void readfile(const char* c) {
	setnoaddr(); if (vflag && fchange) { fchange = 0; /* error(Q); */ } filename(c); init();
	addr2 = zero; if ((io = open((const char*)file, 0)) < 0) { lastc = '\n'; error(file); }
	setwide(); squeeze(0); ninbuf = 0; append(getfile, addr2); exfile(); fchange = *c;
}
void search(const char* c) {
	char buf[256]; snprintf(buf, sizeof(buf), "/%s\n", c);
	const char* p = buf + strlen(buf) - 1; while (p >= buf) { ungetch(*p--); }
	global(1);
}
void search_file(const char* filename, const char* searchfor) {
	readfile(filename);
	search(searchfor);
}
