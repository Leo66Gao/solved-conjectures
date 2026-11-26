// Exhaustively generate unlabeled simple graphs to order eight by vertex extensions.
// Canonical code: first 1-WL stable coloring with canonical color names, then
// minimize the upper-triangle word over every ordering respecting those colors.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using Word=uint32_t;
int bit(int i,int j){if(i>j)swap(i,j);return j*(j-1)/2+i;}
Word canon(int n, Word g) {
    bool a[8][8]={}; for(int i=0;i<n;i++)for(int j=0;j<i;j++) a[i][j]=a[j][i]=(g>>bit(i,j))&1;
    vector<int> c(n,0); while(true){
        vector<array<int,9>> sig(n);for(int i=0;i<n;i++){sig[i].fill(0);sig[i][0]=c[i];for(int j=0;j<n;j++) if(a[i][j]) sig[i][1+c[j]]++;}
        auto uniq=sig;sort(uniq.begin(),uniq.end());uniq.erase(unique(uniq.begin(),uniq.end()),uniq.end());
        vector<int>d(n);for(int i=0;i<n;i++) d[i]=lower_bound(uniq.begin(),uniq.end(),sig[i])-uniq.begin();
        if(c==d)break;c=d;
    }
    vector<vector<int>> groups(*max_element(c.begin(),c.end())+1);
    for(int i=0;i<n;i++) groups[c[i]].push_back(i);
    array<int,8> p{};Word best=UINT32_MAX;
    auto walk=[&](auto&& self,int j,int pos)->void{
        if(j==int(groups.size())){Word w=0;for(int y=0;y<n;y++)for(int x=0;x<y;x++)if(a[p[x]][p[y]])w|=1u<<bit(x,y);best=min(best,w);return;}
        auto& v=groups[j];do {copy(v.begin(),v.end(),p.begin()+pos);self(self,j+1,pos+v.size());}while(next_permutation(v.begin(),v.end()));
    };walk(walk,0,0);return best;
}
int main(){
    set<Word> prev{0};cout<<"1 0\n";
    const int counts[]={0,1,2,4,11,34,156,1044,12346};
    for(int n=2;n<=8;n++){set<Word> curr;for(Word w:prev) for(Word e=0;e<(1u<<(n-1));e++)curr.insert(canon(n,w|(e<<((n-1)*(n-2)/2))));
        if(curr.size()!=size_t(counts[n]))return 1;
        for(Word w:curr)cout<<n<<' '<<w<<'\n';prev=move(curr);}
}
