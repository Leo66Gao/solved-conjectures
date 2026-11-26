// Heuristic search for periodic tilings by strong balanced Q12 cell shapes.
// g++ -O3 -march=native -std=c++17 tile12.cpp -o tile12; ./tile12 50000
#include "orbit-lib.h"
using U=uint64_t;
using M=array<U,4>;
M join(M a,M b){for(int i=0;i<4;i++)a[i]|=b[i];return a;}
inline int ctbits(M a){return __builtin_popcountll(a[0])+__builtin_popcountll(a[1])+__builtin_popcountll(a[2])+__builtin_popcountll(a[3]);}
inline void setbit(M& a,int x){a[x>>6]|=1ULL<<(x&63);}
struct Polar {array<int,64>S;M a[256];};
int main(int ac,char**av){
 n=12;r=8;d=4;N=1<<n;T=256;K=4;R.seed(20172451);
 int trials=atoi(av[1]),hit=0,best_cover=0,allmax=0, strict_trials=0; double top=0,strict=0;
 for(int e=0;e<N;e++)for(int i=0;i<n;i++)sg[e][i]=1-2*(e>>i&1);iota(ord,ord+T,0);
 vector<array<int,64>> shape;ifstream in("good-n12.txt");
 array<int,64> S;while(in>>S[0]){for(int j=1;j<64;j++){in>>S[j];assert(in);}shape.push_back(S);}assert(shape.size()==12);
 for(int tr=0;tr<trials;tr++){
  int used[256]={};for(int j=0;j<r;j++)col[j]=1<<j,used[col[j]]=1;
  for(int j=r;j<n;j++){int a;do a=1+R()%255;while(used[a]||(tr%2&&__builtin_parity(a)==0));col[j]=a;used[a]=1;}
  sy[0]=0;for(int e=1;e<N;e++)sy[e]=sy[e&(e-1)]^col[__builtin_ctz(e)];
  vector<Polar> cand;
  for(int i=0;i<96;i++){
   auto t=shape[R()%shape.size()];array<int,12>P;iota(P.begin(),P.end(),0);shuffle(P.begin(),P.end(),R);
   Polar p;M M0={};
   for(int j=0;j<64;j++){
    int e0=t[j],e=0;while(e0){int k=__builtin_ctz(e0);e|=1<<P[k];e0&=e0-1;}
    p.S[j]=e;setbit(M0,sy[e]);
   }
   if(ctbits(M0)!=64)continue;
   for(int q=0;q<256;q++){p.a[q]={};for(int e:p.S)setbit(p.a[q],sy[e]^q);}
   cand.push_back(p);
  }
  int c=cand.size();if(!c)continue;hit++;
  int gb=0,bi[4],bt[4];
  for(int h=0;h<3;h++){
   int a[4],t[4];M u[4];for(int i=0;i<4;i++)a[i]=R()%c,t[i]=i==0?0:R()%256,u[i]=cand[a[i]].a[t[i]];
   for(int rep=0;rep<10;rep++){
    int moves=0;int p[4]={0,1,2,3};shuffle(p,p+4,R);
    for(int i:p){
     M P={};for(int j=0;j<4;j++)if(i!=j)P=join(P,u[j]);
     int bs=ctbits(join(P,u[i])),ba=a[i],bt=t[i];
     for(int k=0;k<c;k++)for(int v=0;v<256;v++){int s=ctbits(join(P,cand[k].a[v]));if(s>bs)bs=s,ba=k,bt=v;}
     if(ba!=a[i]||bt!=t[i])moves++,a[i]=ba,t[i]=bt,u[i]=cand[ba].a[bt];
    }
    if(!moves)break;
   }
   M all={};for(int i=0;i<4;i++)all=join(all,u[i]);int cv=ctbits(all);
   if(cv>gb){gb=cv;copy(a,a+4,bi);copy(t,t+4,bt);}
  }
  if(gb>best_cover){best_cover=gb;cout<<"trial "<<tr<<" cover "<<gb<<"\n"<<flush;}
  if(gb<225)continue;
  prep();copy(bt,bt+4,cen);reset();
  double mu[4][16];for(int a=0;a<4;a++)for(int i=0;i<n;i++){mu[a][i]=0;for(int e:cand[bi[a]].S)mu[a][i]+=sg[e][i]/64.;}
  for(int t=0;t<T;t++){
   double best=-1e6;int ea=-1,aa=-1;
   for(int a=0;a<4;a++)for(int e:cosets[t^cen[a]]){
    double z=0;for(int i=0;i<n;i++)z+=2*mu[a][i]*sg[e][i]-mu[a][i]*mu[a][i];
    if(z>best){best=z;ea=e;aa=a;}
   }
   q[t]=aa;er[t]=ea;update(aa,ea,1);
  }
  double B=ascend();strict_trials++;
  if(B>top+1e-10||(B<6-1e-10&&B>strict+1e-10)){
   top=max(top,B);if(B<6-1e-10)strict=max(strict,B);
   cout<<"trial "<<tr<<" B "<<setprecision(15)<<B<<" cover "<<gb<<"\n"<<flush;
   FILE*f=fopen("tile12-best.txt","w");fprintf(f,"%d %d\n",n,d);for(int j=0;j<n;j++)fprintf(f,"%d ",col[j]);fputs("\n",f);for(int a=0;a<K;a++)fprintf(f,"%d ",cen[a]);fputs("\n",f);for(int i=0;i<T;i++)fprintf(f,"%d %d\n",q[i],er[i]);fclose(f);
  }
  if(B>6+1e-8){cout<<"CANDIDATE "<<tr<<" "<<setprecision(15)<<B<<"\n"<<flush;break;}
  }
 cout<<"Finished "<<trials<<" trials; covering record "<<best_cover<<"; any valid projection "<<hit<<"; refined "<<strict_trials<<"; best "<<setprecision(15)<<top<<"; best strict below "<<strict<<endl;
}
