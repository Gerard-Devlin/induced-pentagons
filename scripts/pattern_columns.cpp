// Exact injection counts for the seven-vertex pentagon certificate columns.
// Reconstructed from equations (9), (10), (11), and Section 4 of the PDF.
// This enumerates integer counts only; it does not assert an SDP certificate.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

struct Pattern {
    std::string name;
    int n;
    std::uint32_t edges, nonedges;
};

static int bit_index(int n, int i, int j) {
    if (i > j) std::swap(i,j);
    if (i == j) throw std::runtime_error("loop requested in bit_index");
    return i*(2*n-i-1)/2+j-i-1;
}

static std::uint64_t clebsch_hom_count(const Pattern& p) {
    // Every requested pattern has no isolated required-edge vertex. Hence
    // isolated graphon mass contributes zero, and all 16 active classes
    // have numerator one in the reference weighting 1/48.
    std::array<std::array<int,7>,7> req{};
    std::array<int,7> degree{};
    for(int i=0;i<p.n;++i) for(int j=i+1;j<p.n;++j) {
        const auto b=std::uint32_t(1)<<bit_index(7,i,j);
        req[i][j]=req[j][i]=(p.edges&b)?1:((p.nonedges&b)?-1:0);
        if(req[i][j]==1) {++degree[i];++degree[j];}
    }
    for(int i=0;i<p.n;++i)
        if(degree[i]==0) throw std::runtime_error("isolated pattern vertex");
    std::array<std::array<bool,16>,16> adjacent{};
    for(int x=0;x<16;++x) for(int y=0;y<16;++y) {
        int d=x^y;
        adjacent[x][y]=(d==1 || d==2 || d==4 || d==8 || d==15);
    }
    // Greedy ordering keeps a required-edge frontier and sharply prunes
    // the homomorphism enumeration; repeated class assignments are allowed.
    std::vector<int> order;
    std::array<bool,7> used{};
    while(int(order.size())<p.n) {
        int best=-1,bestscore=-1;
        for(int v=0;v<p.n;++v) if(!used[v]) {
            int score=degree[v];
            for(int u:order) score+=100*(req[u][v]==1)+10*(req[u][v]==-1);
            if(score>bestscore) {best=v;bestscore=score;}
        }
        used[best]=true;order.push_back(best);
    }
    std::array<int,7> assignment{};
    std::function<std::uint64_t(int)> visit=[&](int depth)->std::uint64_t {
        if(depth==p.n) return 1;
        const int v=order[depth];
        std::uint64_t total=0;
        for(int x=0;x<16;++x) {
            bool okay=true;
            for(int k=0;k<depth;++k) {
                const int u=order[k],r=req[u][v];
                const bool a=adjacent[assignment[u]][x];
                if((r==1 && !a)||(r==-1 && a)) {okay=false;break;}
            }
            if(okay) {assignment[v]=x;total+=visit(depth+1);}
        }
        return total;
    };
    return visit(0);
}

int main(int argc,char**argv) {
    if(argc!=5) {
        std::cerr<<"usage: pattern_columns HOST_MASKS PATTERNS CANONICAL5 OUTPUT\n";
        return 2;
    }
    try {
        std::ifstream hs(argv[1]),ps(argv[2]),cs(argv[3]);
        if(!hs||!ps||!cs) throw std::runtime_error("cannot open input");
        std::vector<std::uint32_t> hosts;
        std::uint32_t h;
        while(hs>>h) hosts.push_back(h);
        std::vector<Pattern> patterns;
        Pattern p;
        while(ps>>p.name>>p.n>>p.edges>>p.nonedges) patterns.push_back(p);
        std::array<int,1024> canon{};
        for(int i=0;i<1024;++i)
            if(!(cs>>canon[i])) throw std::runtime_error("canonical5 truncated");
        std::vector<std::array<int,21>> perm_maps;
        std::array<int,7> perm={0,1,2,3,4,5,6};
        do {
            std::array<int,21> m{};
            int b=0;
            for(int i=0;i<7;++i) for(int j=i+1;j<7;++j)
                m[b++]=bit_index(7,perm[i],perm[j]);
            perm_maps.push_back(m);
        }while(std::next_permutation(perm.begin(),perm.end()));
        const std::array<int,8> fact={1,1,2,6,24,120,720,5040};
        std::ofstream out(argv[4]);
        if(!out) throw std::runtime_error("cannot open output");
        out<<hosts.size()<<" "<<patterns.size()<<"\n";
        for(const auto host:hosts) {
            std::vector<std::uint64_t> count(patterns.size(),0);
            for(const auto&m:perm_maps) {
                std::uint32_t relabeled=0;
                for(int b=0;b<21;++b) relabeled|=((host>>m[b])&1u)<<b;
                for(std::size_t k=0;k<patterns.size();++k) {
                    const auto&pt=patterns[k];
                    if((relabeled&pt.edges)==pt.edges &&
                       (relabeled&pt.nonedges)==0) ++count[k];
                }
            }
            std::array<int,34> induced{},paired{};
            for(int a=0;a<7;++a) for(int b=a+1;b<7;++b) {
                std::array<int,5> v{};int at=0;
                for(int t=0;t<7;++t) if(t!=a&&t!=b) v[at++]=t;
                int mask5=0,bit=0;
                for(int i=0;i<5;++i) for(int j=i+1;j<5;++j)
                    mask5|=((host>>bit_index(7,v[i],v[j]))&1u)<<bit++;
                const int id=canon[mask5];
                ++induced[id];
                if((host>>bit_index(7,a,b))&1u) ++paired[id];
            }
            out<<host;
            for(std::size_t k=0;k<patterns.size();++k) {
                const auto multiplicity=fact[7-patterns[k].n];
                if(count[k]%multiplicity)
                    throw std::runtime_error("injection divisibility failed");
                out<<" "<<count[k]/multiplicity;
            }
            for(int n:induced) out<<" "<<n;
            for(int n:paired) out<<" "<<n;
            out<<"\n";
        }
        out<<"CLEBSCH";
        for(const auto&pt:patterns) out<<" "<<clebsch_hom_count(pt);
        out<<"\n";
        std::cerr<<"Counted "<<hosts.size()<<" hosts, "<<patterns.size()
                 <<" patterns and 34 fixed-density columns exactly.\n";
        return 0;
    }catch(const std::exception&e) {
        std::cerr<<"error: "<<e.what()<<"\n";
        return 1;
    }
}
