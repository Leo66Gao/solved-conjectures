#include<bits/stdc++.h>
using namespace std;
mt19937 R; int n,d,r,T,K,mask,N,sy[65536],col[16],cen[32],q[1024],er[1024],ct[32],s[32][16],ss[32],ord[1024],pen[65536];vector<int> cosets[1024];alignas(32) signed short sg[65536][16],sh[32][16];
int ip(int a,int e){int z=0;for(int i=0;i<16;i++)z+=sh[a][i]*sg[e][i];return z;}
int val(int a){int z=0;for(int i=0;i<n;i++)z+=sh[a][i]*sh[a][i];return z;}
void update(int a,int e,int dd){for(int i=0;i<n;i++)sh[a][i]+=dd*sg[e][i];ct[a]+=dd;ss[a]=val(a);}
void reset(){memset(sh,0,sizeof(sh));memset(ct,0,sizeof(ct));memset(ss,0,sizeof(ss));}
void prep(){for(int t=0;t<T;t++)cosets[t].clear();sy[0]=0;for(int e=0;e<N;e++){if(e)sy[e]=sy[e&(e-1)]^col[__builtin_ctz(e)];cosets[sy[e]].push_back(e);}}
void ini(int trial){
 vector<int> w(n);for(auto&u:w)u=100000+(trial%3==0?0:trial%3==1?(int)(R()%100):(int)(R()%30000));for(int e=1;e<N;e++)pen[e]=pen[e&(e-1)]+w[__builtin_ctz(e)];vector<int> cc(T);iota(cc.begin(),cc.end(),0);shuffle(cc.begin(),cc.end(),R);for(int a=0;a<K;a++)cen[a]=cc[a];
 reset();for(int t=0;t<T;t++){int st=INT_MAX,a0=-1,e0=-1;for(int a=0;a<K;a++)for(int e:cosets[t^cen[a]]){int u=pen[e];if(u<st||u==st&&e<e0){st=u;a0=a;e0=e;}}q[t]=a0;er[t]=e0;update(a0,e0,1);}
}
double ascend(int maxit=35){for(int it=0;it<maxit;it++){shuffle(ord,ord+T,R);int moves=0;for(int l=0;l<T;l++){int t=ord[l],a0=q[t],e0=er[t];int a1=a0,e1=e0;update(a0,e0,-1);double hi=(2.*ip(a0,e0)+n-(ct[a0]?ss[a0]/(double)ct[a0]:0.))/(ct[a0]+1);for(int a=0;a<K;a++){int m=ct[a];double off=n-(m?ss[a]/double(m):0); int best=-1,bv=INT_MIN;for(int e:cosets[t^cen[a]]){int f=ip(a,e);if(f>bv){bv=f;best=e;}}double z=(2*bv+off)/(m+1);if(z>hi+1e-9){hi=z;a1=a;e1=best;}}q[t]=a1;er[t]=e1;update(a1,e1,1);moves+=(a1!=a0||e1!=e0);}if(!moves)break;}
 double B=0;for(int j=0;j<K;j++)if(ct[j])B+=ss[j]/double(ct[j]);return B/T;}
void shake(int k){for(int u=0;u<k;u++){int t=R()%T;update(q[t],er[t],-1);int a=R()%K;auto &v=cosets[t^cen[a]];int e=v[R()%v.size()];q[t]=a;er[t]=e;update(a,e,1);}}
int orbit_main(int ac,char**av){n=atoi(av[1]);d=atoi(av[2]);r=n-d;T=1<<r;K=1<<(6-d);N=1<<n;assert(T<=1024&&K<=32&&n<=16);R.seed(19335107+104*n+d);
 for(int e=0;e<N;e++)for(int i=0;i<n;i++)sg[e][i]=1-2*(e>>i&1);iota(ord,ord+T,0);double top=-1;int bestcol[16];int trials=atoi(av[3]);
 for(int i=0;i<trials;i++){int mode=R()%6,used[1024]={};for(int j=0;j<r;j++)col[j]=1<<j,used[col[j]]=1;
  for(int j=r;j<n;j++){int c=0;if(i%4==3)c=bestcol[j];if(!c||j==r+R()%d){do c=1+R()%(T-1);while(mode>0&&used[c]|| mode==5&&__builtin_popcount((unsigned)c)%2==0);}col[j]=c;used[c]=1;}prep();
  for(int k=0;k<3;k++){ini(i+k);for(int h=0;h<3;h++){double B=ascend();if(B>top+1e-8){top=B;copy(col,col+n,bestcol);printf("n %d d %d trial %d B %.12f m",n,d,i,B);for(int a=0;a<K;a++)printf(" %d",ct[a]);puts("");fflush(stdout);FILE*f=fopen(("orbit-"+to_string(n)+"-"+to_string(d)+".cert").c_str(),"w");fprintf(f,"%d %d\n",n,d);for(int j=0;j<n;j++)fprintf(f,"%d ",col[j]);fputs("\n",f);for(int a=0;a<K;a++)fprintf(f,"%d ",cen[a]);fputs("\n",f);for(int t=0;t<T;t++)fprintf(f,"%d %d\n",q[t],er[t]);fclose(f);if(B>6.000001)return 0;}shake(1+R()%(T/10+1));}}
 }
}
