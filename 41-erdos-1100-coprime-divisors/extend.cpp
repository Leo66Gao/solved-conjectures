#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
#include "extend.hpp"
int main(int argc,char** argv) {
  int k=argc>1?stoi(argv[1]):6; assert(k>0&&k<=7);
  if(argc>=3)TARGET=stoi(argv[2]);
  int n=1<<k,M=n-1, best=0; long long count=0;
  string start(n,0); for(int i=0;i<n;i++)start[i]=char(i);
  unordered_set<string> visited={start};
  vector<string> stack={start};
  vector<long long> h(n+1);
  while(!stack.empty()) {
    string s=stack.back(); stack.pop_back();
    array<int,128> pos{}; for(int i=0;i<n;i++)pos[(unsigned char)s[i]]=i;
    int score=0; for(int i=1;i<n;i++) score+=!(s[i-1]&s[i]);
    test7(s);h[score]++; count++;
    if(score>best){best=score; cerr<<"new "<<best<<" after "<<count<<"\n"; cout<<"best "<<best<<" :";for(auto v:s)cout<<" "<<int((unsigned char)v);cout<<endl;}
    for(int i=1;i<n;i++) {
      int a=(unsigned char)s[i-1],b=(unsigned char)s[i];
      if(a&b || !a || (! (a&(a-1)) && !(b&(b-1))))continue;
      int un=M^(a|b), t=un;
      while(t && pos[a|t]+1==pos[b|t])t=(t-1)&un;
      if(t)continue;
      string next=s;
      t=un;
      do {swap(next[pos[a|t]],next[pos[b|t]]); if(!t)break; t=(t-1)&un;}while(true);
      if(visited.insert(next).second)stack.push_back(next);
    }
  }
  cout<<"bases "<<bases<<" nodes "<<nodes<<" leaves "<<leaves<<endl; cout<<"states "<<count<<" max "<<best<<"\n";for(int i=0;i<=best;i++)if(h[i])cout<<"score "<<i<<" : "<<h[i]<<'\n';
}
