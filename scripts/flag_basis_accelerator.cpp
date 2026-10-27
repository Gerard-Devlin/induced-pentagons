// Exact finite enumeration for build_flag_basis.py.
// All graph-mask bits are lexicographic pairs i<j; root labels remain fixed.
#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>

namespace {
int pair_bit(int i, int j, int n) {
    if (i > j) std::swap(i, j);
    return i*(2*n-i-1)/2 + j-i-1;
}

uint32_t induced_mask(const int *vertices, int n, const int adj[17][17]) {
    uint32_t mask = 0;
    int bit = 0;
    for (int i=0; i<n; ++i)
        for (int j=i+1; j<n; ++j, ++bit)
            if (adj[vertices[i]][vertices[j]]) mask |= uint32_t(1)<<bit;
    return mask;
}
}

extern "C" void canonical7(const uint32_t *masks, int count,
                            uint32_t *canonical, uint32_t *automorphisms) {
    std::vector<std::array<uint32_t,21>> transformations;
    std::array<int,7> p{{0,1,2,3,4,5,6}};
    do {
        std::array<uint32_t,21> t;
        int bit = 0;
        for (int i=0; i<7; ++i)
            for (int j=i+1; j<7; ++j, ++bit)
                t[bit]=uint32_t(1)<<pair_bit(p[i],p[j],7);
        transformations.push_back(t);
    } while (std::next_permutation(p.begin(),p.end()));
    for (int h=0; h<count; ++h) {
        uint32_t best=uint32_t(1)<<21, multiplicity=0;
        for (const auto &t:transformations) {
            uint32_t input=masks[h], image=0;
            while (input) {
                int bit=__builtin_ctz(input);
                image |= t[bit];
                input &= input-1;
            }
            if (image<best) { best=image; multiplicity=1; }
            else if (image==best) ++multiplicity;
        }
        canonical[h]=best;
        automorphisms[h]=multiplicity;
    }
}

extern "C" void host_flag_counts(const uint32_t *hosts, int host_count,
                                  int roots, int root_signature, int dimension,
                                  const int32_t *flag_lookup,
                                  int32_t *counts) {
    for (int h=0; h<host_count; ++h) {
        int adj[17][17]={};
        int bit=0;
        for (int i=0;i<7;++i)
            for (int j=i+1;j<7;++j,++bit)
                adj[i][j]=adj[j][i]=(hosts[h]>>bit)&1;
        int32_t *out=counts+int64_t(h)*dimension*dimension;
        if (roots==1) {
            for (int r=0;r<7;++r) {
                int available[6],pos=0;
                for (int i=0;i<7;++i) if(i!=r) available[pos++]=i;
                for (int i=0;i<4;++i)
                    for (int j=i+1;j<5;++j)
                        for (int k=j+1;k<6;++k) {
                            int v[4]={r,available[i],available[j],available[k]};
                            int w[4]={r,0,0,0}, q=1;
                            for (int s=0;s<6;++s)
                                if(s!=i&&s!=j&&s!=k) w[q++]=available[s];
                            int a=flag_lookup[induced_mask(v,4,adj)];
                            int b=flag_lookup[induced_mask(w,4,adj)];
                            ++out[a*dimension+b];
                        }
            }
        } else {
            for (int r0=0;r0<7;++r0)
                for (int r1=0;r1<7;++r1) if(r1!=r0)
                    for (int r2=0;r2<7;++r2) if(r2!=r0&&r2!=r1) {
                        int sig=adj[r0][r1]+2*adj[r0][r2]+4*adj[r1][r2];
                        if(sig!=root_signature) continue;
                        int available[4],pos=0;
                        for(int i=0;i<7;++i)
                            if(i!=r0&&i!=r1&&i!=r2) available[pos++]=i;
                        for(int i=0;i<3;++i)
                            for(int j=i+1;j<4;++j) {
                                int v[5]={r0,r1,r2,available[i],available[j]};
                                int w[5]={r0,r1,r2,0,0},q=3;
                                for(int s=0;s<4;++s)
                                    if(s!=i&&s!=j) w[q++]=available[s];
                                int a=flag_lookup[induced_mask(v,5,adj)];
                                int b=flag_lookup[induced_mask(w,5,adj)];
                                ++out[a*dimension+b];
                            }
                    }
        }
    }
}

extern "C" int equality_flag_rows(int roots, int root_signature, int dimension,
                                   const int32_t *flag_lookup,
                                   int64_t *rows, int32_t *root_assignments) {
    int adj[17][17]={};
    const int gen[5]={1,2,4,8,15};
    for(int i=0;i<16;++i)
        for(int s:gen) adj[i][i^s]=1;
    auto weight=[](int vertex)->int64_t{return vertex==16?32:1;};
    int row_count=0;
    if(roots==1) {
        for(int r=0;r<17;++r) {
            int64_t *out=rows+int64_t(row_count)*dimension;
            root_assignments[row_count]=r;
            for(int a=0;a<17;++a)
                for(int b=0;b<17;++b)
                    for(int c=0;c<17;++c) {
                        int v[4]={r,a,b,c};
                        int f=flag_lookup[induced_mask(v,4,adj)];
                        out[f]+=weight(a)*weight(b)*weight(c);
                    }
            ++row_count;
        }
    } else {
        for(int r0=0;r0<17;++r0)
            for(int r1=0;r1<17;++r1)
                for(int r2=0;r2<17;++r2) {
                    int sig=adj[r0][r1]+2*adj[r0][r2]+4*adj[r1][r2];
                    if(sig!=root_signature) continue;
                    int64_t *out=rows+int64_t(row_count)*dimension;
                    root_assignments[3*row_count]=r0;
                    root_assignments[3*row_count+1]=r1;
                    root_assignments[3*row_count+2]=r2;
                    for(int a=0;a<17;++a)
                        for(int b=0;b<17;++b) {
                            int v[5]={r0,r1,r2,a,b};
                            int f=flag_lookup[induced_mask(v,5,adj)];
                            out[f]+=weight(a)*weight(b);
                        }
                    ++row_count;
                }
    }
    return row_count;
}
