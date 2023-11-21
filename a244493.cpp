/*
   Computation of OEIS Sequence A244493

   An equivalent form of the sequence in term of restricted permutations is:
      Let X be the set of all 2-element subsets of {1,...,n}.  
      How many permutations f of X are there such that for any A in X, f(A) is not disjoint from A?

   Using several levels of the inclusion-exclusion principle, this problem breaks down into a 
   large number of image_configurations that are faster to solve on a computer.

   Instead of 1..n we use ABC.. so that two-element subsets can be denoted as AB AC BC etc. 
   and are readily distinguished from numerals.

   For details on the mathematical formulas and algorithms that this program is based on,
   please see the A244493.pdf document.

   (C) 2017 Ronald S Niles, permissions granted under the GPL 3.0 License

   Tested on Ubuntu Linux 16.04 LTS 64-bit.
   Requires installation of boost package, 
      sudo apt-get install libboost-all-dev
   Compile: 
      g++ -O3 -o a244493 a244493.cpp
*/

#include <iostream>
#include <fstream>
#include <stdexcept>
#include <iomanip>
#include <sstream>
#include <list>
#include <vector>
#include <map>
#include <set>
#include <string>
#include <bitset>
#include <algorithm>

#include <boost/cstdint.hpp>
#include <boost/foreach.hpp>
#include <boost/lexical_cast.hpp>

/* define CHECK64BIT_OVERFLOW to enable 64-bit overflow check in the tight-inner loop. The 
   program's already been run through n=8 and didn't trigger the overflow, so no need to check again */
//#define CHECK64BIT_OVERFLOW

/* Using multiprecision integers from the BOOST package because coefficients are getting larger 
   than 64-bits for n=7 */
#include <boost/multiprecision/cpp_int.hpp>
typedef boost::multiprecision::int256_t multiprecision;

/* flag to solve the complementary problem instead (which can be used to verify the results) */
bool bcomplementary = false; 

/* the initial set 1...n, specify n as "nsetsize" */
unsigned nsetsize;

/* number of two-element subsets, i.e. "nsetsize" choose two */
unsigned nsubsets;

/* running total of the results broken down by size and multiplicity pattern */
std::map<unsigned, std::map<std::vector<unsigned>, multiprecision> > results_by_size;

/* pascal's triangle - needed for indexing bitmap permutations */
std::vector<std::vector<unsigned> > pascalt;

void make_pascal_triangle(void) {
   pascalt.clear();
   pascalt.resize(nsubsets+1);
   pascalt[0].push_back(1);
   for (unsigned i=1; i<=nsubsets; ++i) {
      pascalt[i].push_back(pascalt[i-1][0]);
      for (unsigned j=1; j<pascalt[i-1].size(); ++j) {
         pascalt[i].push_back(pascalt[i-1][j-1] + pascalt[i-1][j]);
      }
      pascalt[i].push_back(pascalt[i-1].back());
   }
}

/* given a bitmap with ntotal bits and nsetbits, return the rank (position in the ordered
set of all possible bitmaps with ntotal bits and nsetbits) */
unsigned rank_from_permutation(unsigned bitmap, unsigned ntotbits, unsigned nsetbits) {
   unsigned total = 0;
   unsigned row = ntotbits;
   unsigned col = row - nsetbits;
   unsigned thisbit = 1 << (ntotbits-1);
   for(;;) {
      if (pascalt[row][col] == 1) {
         break;
      }
      row--;
      if (bitmap & thisbit) {
         total += pascalt[row][col-1];
      } else {
         col--;
      }
      thisbit >>= 1;
   }
   return total;
}

/* returns the nth bit permutation with ntotbits and nsetbits, i.e. if all such
permutations are put in order and ranked starting from zero, what is bit permutation at position "rank"? */
unsigned permutation_from_rank(unsigned rank, unsigned ntotbits, unsigned nsetbits) {
   unsigned res = 0;
   unsigned row = ntotbits;
   unsigned col = row - nsetbits;
   unsigned thisbit = 1 << (ntotbits-1);
   for(;;) {
      if (row-- == 0) break;
      if (col > 0 && rank < pascalt[row][col-1]) {
         --col;
      } else {
         if (col) rank -= pascalt[row][col-1];
         res |= thisbit;
      }
      thisbit >>= 1;
   }
   return res;
}

/* memory to hold the intermediate image_configuration results as we are computing them.
   To compute n=8 this structure will allocate 2GiB of working memory.
   It is efficient because it is linear: the data for each bitset is based on the rank
   of the bitset's bit permutation and is put in that position in the vector, so only
   the 64-bit value associated with the bitset is taking up any memory
*/

std::vector<std::vector<boost::uint64_t> > icfg_memory;

void make_icfg_memory(void) {
   for(unsigned i=0; i<=nsubsets; ++i) {
      icfg_memory.push_back(std::vector<boost::uint64_t>());
      /* each vector will be resized to the number of bitmaps with i bits */
      icfg_memory.back().resize(pascalt[nsubsets][i]);
   }
}

/* The stack, which will be a sequence of image configurations which build upon the previous. */

class icfg_stack_t {
public:
   icfg_stack_t(unsigned n) : nbits(n), nvalues(pascalt[nsubsets][n]), divisor(0) { }
   unsigned nbits; /* number of bits for each bitset in this level. Each bit corresponds to a 
                     domain element that has been used */
   unsigned nvalues; /* how many bitsets with nbits set are possible */
   unsigned divisor; /* the algorithm we use to compute the next level counts multiple times
                        depending on certain bits already set, so the divisor indicates the
                        correction to be applied */
   boost::uint64_t res;

   /* The name refers to the specific image_configuration that is being solved in this object. It will
      be something like:
      AcBeGfKd
      This string means, 
         "how many one-to-many mappings "f(x)" of {AB, AC, BC, AD, BD, CD, AE, BE, CE, DE...} to itself
             (use whatever set of two-element subsets is appropriate for your given "n")
         are possible where f(x) is disjoint from (x), and
           2 (c=3rd letter -1) elements map to the pairset encoded as A,
           4 (e=5th letter -1) elements map to the pairset encoded as B,
           5 (f=6th letter -1) elements map to the pairset encoded as G,
           3 (d=4th letter -1) elements map to the pairset encoded as K,

      Since these are fully-multiple mappings, each element will be mapped to at least twice. If the level
      is being used by the main orbit routine (elements near the front of the stack), the small letters will 
      not be used. So a stack might have names like "", "A", "AB", "ABC", "AcBcCcDc", "AcBcCcDd". Note
      that each item in the stack differs by one image element from the previous. This is intentional
      and allows efficient building upon previous results to compute needed results.
   */

   std::string name;

   /* we can use this data structure like a map, i.e. use the [] operator. In the computations 
      scheme being used here, the values to be indexed always have exactly nbits, because we're
      totalling fully multiple maps of a specific domain size, and the bits represent those 
      domain elements. This scheme gets the rank of the bitmap and uses that as an offset into
      the memory, eliminating pointer overhead and tree traversal. */
   boost::uint64_t & operator[](unsigned bm) {
      return icfg_memory[nbits][rank_from_permutation(bm, nsubsets, nbits)];
   }

   /* next_level: the for() loop inside this routine is the "tight inner loop." This does the work
      of computing how many fully multiple mappings of the current size are possible by extending
      previous results by a single domain element, i.e. the size of the mappings increase by 1 */
   boost::uint64_t next_level(icfg_stack_t &prev, unsigned fullbitset) {
      /* zero out the level since we keep running totals */
      memset(&icfg_memory[nbits][0], 0, nvalues * sizeof(boost::uint64_t));

      res = 0;

      /* initialize a bitset with the smallest possible bit permutation with prev.nbits set */
      unsigned bitperm = (1 << prev.nbits) - 1;

      /* go through the existing level of bitmaps */
      for (std::vector<boost::uint64_t>::const_iterator i = icfg_memory[prev.nbits].begin();
         i != icfg_memory[prev.nbits].end(); ++i) 
      {
         boost::uint64_t adjval = *i;
         if (adjval) {
            /* find set of free bits for this destination that can be used */
            unsigned freebits = ~bitperm & fullbitset;
            /* adjust, because this algorithm generates the bitmap multiple times based on bits already there */
            if (prev.divisor) adjval /= prev.divisor;

            unsigned thisbit = 1;
            while(freebits != 0) {
               /* here's the heart of the algorithm. If the bit is not set, that means it's available
                  for use, so we set it and increase the bitset index for the next level by
                  adjval, which represents the entire number of mappings which have the domain represented
                  by the bitperm. */
               if (thisbit & freebits) {
                  freebits ^= thisbit;
                  (*this)[bitperm | thisbit] += adjval;
                  res += adjval;
#ifdef CHECK64BIT_OVERFLOW /* the program's already run through n=8 and didn't trigger this, so it will
                  run slightly faster without it now */
                  if (res < adjval) throw std::runtime_error("64-bit total overflow");
#endif
               }
               thisbit <<= 1; /* check the next bit */
            }
         }
         {
            /* These next two lines of code efficiently compute the lexicographically next bit permutation. 
               This is from the famous "bit-twiddling hacks" by Sean Eron Anderson at Stanford University,
               which are in the public domain. Credit is given to acknowledge that this method is not 
               original work.
            */
            unsigned t = bitperm | (bitperm -1);
#if defined(BOOST_GCC) /* GCC can use __builtin_ctz to access the "count trailing zeros" instruction */
            bitperm = (t+1) | (((~t & -~t) -1) >> (__builtin_ctz(bitperm) + 1));
#else
            /* otherwise get ctz from the boost library - it's not directly exposed but they 
               call it "find_lsb" */
            unsigned long ctz=boost::multiprecision::detail::find_lsb(bitperm);
            bitperm = (t+1) | (((~t & -~t) -1) >> (ctz + 1));
#endif
         }
      }
      return res;
   }
};
std::vector<icfg_stack_t> icfg_stack;

/*
  enumerate_fully_multiple_map_types
  categorize the possible fully multiple mappings of two-element subsets by the multiplicity of each 
  image element, (multiplicities are in descending order, e.g. 3 2 2, not 2 3 2).
  For example AB->EF AC->EF AD->EF CD->AB CE->AB has EF repeated in the image three 
  times (multiplicity 3) and AB twice (multiplicity 2), thus 3 2 is its type
*/
std::set<std::vector<unsigned> > maptypes;
 
void enumerate_fully_multiple_map_types(void) {
   /* the total elements mapped can't be more than nsetsize choose 2 */
   const unsigned max_sum = nsetsize * (nsetsize-1) / 2;

   /* the most any single item can appear as a destination is (nsetsize-2) choose two
    because of image restrictions, any 2-element subset must map to a disjoint 2 element subset */
   const unsigned max_item = (bcomplementary
      ? max_sum - (nsetsize -2) * (nsetsize-3) / 2
      : (nsetsize -2) * (nsetsize-3) / 2 );
   if (max_item < 2) return;

   /* start with the simplest maptype, a single element appearing twice as a destination */
   std::vector<unsigned> vs;
   vs.push_back(2);
   maptypes.insert(vs);

   /* repeatedly go through the existing maptypes and increase the multipliclty until no 
      more maptypes are found */
   for (;;) {
      std::set<std::vector<unsigned> > newstates;
      for (std::set<std::vector<unsigned> >::const_iterator i=maptypes.begin();
         i != maptypes.end(); ++i)
      {
         vs = *i;
         unsigned total = 0;
         for (unsigned j=0; j<vs.size(); ++j) {total += vs[j]; }
         /* if the total is two less than the maximum, we can have another set of two */
         if (total + 2 <= max_sum) {
            vs.push_back(2);
            newstates.insert(vs);
            vs.pop_back();
         }
         /* if the total is one or more less than the maximum, we can increase any single multiplicity value */
         if (total + 1 <= max_sum) {
            for (unsigned j=0; j<vs.size(); ++j) {
               if (vs[j] < max_item && (j==0 || vs[j] != vs[j-1])) {
                  ++vs[j];
                  newstates.insert(vs);
                  --vs[j];
               }
            }
         }
      }
      unsigned oldsize = maptypes.size();
      maptypes.insert(newstates.begin(), newstates.end());
      if (maptypes.size() == oldsize) break;
   }
}

/*
  decode_pattern:
  given a vector of multiplicities, this will provide a decode table for translating orbit strings
  e.g. "aaabbc" to their correct positions in an orbit permutation. 
*/
std::vector<unsigned> decode_pattern(const std::vector<unsigned> &img) {
   std::map<unsigned, unsigned> freq;
   for (unsigned j=0; j<img.size(); ++j) {
      ++freq[img[j]];
   }
   std::multiset<unsigned, std::greater<unsigned> > pat;
   for (std::map<unsigned, unsigned>::const_iterator j = freq.begin(); j!=freq.end(); ++j) {
      pat.insert(j->second);
   }
   std::vector<unsigned> res;
   while(!pat.empty()) {
      unsigned val = *pat.begin();
      pat.erase(pat.begin());
      std::map<unsigned, unsigned>::iterator im;
      for (im = freq.begin(); im != freq.end(); ++im) {
         if (im->second == val) {
            break;
         }
      }
      if (im == freq.end()) throw std::runtime_error("decode pattern error");
      res.push_back(im->first);
      freq.erase(im);
   }
   return res;
}

/*
  map_pattern:
  given a vector of multiplicities, this will provide a pattern based on small letters of 
  the alphabet showing the number of times each multiplicity value appears
*/
std::string map_pattern(const std::vector<unsigned> &img) {

   /* first a frequency showing how many times each multiplicity value occurs */
   std::map<unsigned, unsigned> freq;
   for (unsigned j=0; j<img.size(); ++j) {
      ++freq[img[j]];
   }

   /* then sort the frequencies ascending */
   std::multiset<unsigned, std::greater<unsigned> > pat;
   for (std::map<unsigned, unsigned>::const_iterator j = freq.begin(); j!=freq.end(); ++j) {
      pat.insert(j->second);
   }

   /* then translate the sorted frequencies into strings of small letters which each represent 
      a multiplicity in the vector that was provided. This will be something like "aaaabbc" 
      (characters ascending, length of character runs nondescending) */
   std::string s;
   char ch = 'a';
   for (std::multiset<unsigned, std::greater<unsigned> >::const_iterator j = pat.begin(); j!=pat.end(); ++j) {
      s.append(*j, ch++);
   }
   return s;
}

typedef std::vector<std::vector<unsigned> > image_grouped_t;
typedef std::map<std::string, image_grouped_t> image_pattern_t;
std::map<unsigned, image_pattern_t > image_by_orbit;

/* find_map_patterns: go through all of the maptypes, get the map pattern for each,
   which will be something like "aaaabbc" (characters ascending, length of character
   runs nondescending), and put them in the image_by_orbit data structure. Here's an 
   example for n=5 for what the image_by_orbit structure looks like. It's first by
   size of the map image, next by pattern of multiplicities, next by actual multiplicities
   fitting the pattern.
1
  a
      2
      3
2
  aa
      2 2
      3 3
  ab
      3 2
3
  aaa
      2 2 2
      3 3 3
  aab
      3 2 2
      3 3 2
4
  aaaa
      2 2 2 2
  aaab
      3 2 2 2
  aabb
      3 3 2 2
5
  aaaaa
      2 2 2 2 2
*/

void find_map_patterns(void) {
   image_by_orbit.clear();
   for (std::set<std::vector<unsigned> >::const_iterator i=maptypes.begin(); i != maptypes.end(); ++i)
   {
      std::string s = map_pattern(*i);
      if (s.size() != i->size()) throw std::runtime_error("size mismatch in generating patterns");
      image_by_orbit[s.size()][s].push_back(*i);
   }
}

/* orbits finder object. Start with the mainorbit, which is based on the subset of elements in
   a map image without regards to multiplicity. The purpose of this class is to find
   orbits which are based on the original main orbit but include multiplicities. For example,
   if the main orbit is {AB AC BC}, and the multiplicities are {2 3 4}, each permutation of the
   multiplicities will yield image configurations which evaluate identically because {AB AC BC} is
   highly symmetric. So we only need to evaluate AB02AC03BC04 because other permutations such as
   AB03AC04BC02 will have the same number of mappings. */
class orbits_finder {
public:
   /* constructor takes the main orbit */
   orbits_finder(const std::string &m) : mainorbit(m) {
      /* find the set of characters used by all elements in the main orbit (so we can permute them) */
      std::set<char> usedch;
      for (std::string::const_iterator i= m.begin(); i!= m.end(); ++i) {
         usedch.insert(*i);
      }

      /* set up an xlat vector from the sorted characters, so the xlat vector can go
         through all of its permutations and act on the mainorbit */
      std::vector<char> xlat;
      for (std::set<char>::const_iterator i = usedch.begin(); i != usedch.end(); ++i) {
         xlat.push_back(*i);
      }

      do {
         std::set<std::string> newstr;
         /* go through each two-letter segment of the main orbit, translating
         characters according to the permutation in xlat */
         for(unsigned i=0; i<mainorbit.size(); i+=2) {
            std::string s1;
            s1.push_back(xlat[mainorbit[i]-'A']);
            s1.push_back(xlat[mainorbit[i+1]-'A']);
            s1.push_back('a'+i/2);  /* also attach letters a,b,c,d... in sequence to the initial arrangement */
            if (s1[0] > s1[1]) std::swap(s1[0], s1[1]); /* we must keep the translated two-letter segment in ascending order */
            newstr.insert(s1); /* insert to a set, so we can reassemble the translated orbit in lexicographic order */
         }
         /* reassemble the translated orbit in lexicographic order */
         std::string s1, s2;
         for (std::set<std::string>::const_iterator i = newstr.begin(); i != newstr.end(); ++i) {
            s1 += i->substr(0,2);
            s2 += (*i)[2];
         }
         /* we're only interested in permutations that are part of the kernel of the group action,
            in other words the permutation preserves the mainorbit subset */
         if (s1 == mainorbit) {
            /* now find the permutation that was induced on the mainorbit by this permutation, and
               save it in the set. There could be many permutations on the mainorbit that induce
               identical permutatons so the induced permutations are kept in a set to sort and 
               eliminate duplicates */
            std::vector<unsigned char> newinduced;
            for (unsigned k=0; k< s2.size(); ++k) {
               newinduced.push_back(s2.find('a'+k));
            }
            induced.insert(newinduced);
         }
      } while(next_permutation(xlat.begin(), xlat.end()));
   }

   /* find all orbits of a map_pattern. The map_pattern will be run through all of its permutations,
     and those permutations of the map pattern will be grouped into orbits by letting the 
     induced permutations of the main orbit act on that set */
   void find_orbits(const std::string &nd) {
      orbits.clear();
      if (nd.size() *2 != mainorbit.size()) throw std::runtime_error("orbit size mismatch");
      /* go through all of the permutations of the map_pattern */
      std::string nd2 = nd;
      do {
         if (!already(nd2)) { /* if it's not already in one of the orbits */
            new_orbit(nd2);   /* then set up a new orbit for it */
         }
      } while(next_permutation(nd2.begin(), nd2.end()));
   }
   /* see if the string is already in one of the orbits by searching each orbit in sequence */
   bool already(const std::string &s) {
      for (unsigned i=0; i< orbits.size(); ++i) {
         if (orbits[i].find(s) != orbits[i].end()) {
            return true;
         }
      }
      return false;
   }
   /* set up a new orbit for a string which was not found in any of the existing orbits */
   void new_orbit(const std::string &s) {
      /* push back an empty set to the end of the orbit vector. We will add to this set */
      orbits.push_back(std::set<std::string>());

      /* Let the induced permutations act upon the string, and insert each of the permuted versions
         of the string into the set. Some of them may be duplicates, the set will remove those */
      for (std::set<std::vector<unsigned char> >::const_iterator i = induced.begin(); i != induced.end(); ++i) {
         std::string s2;
         for (unsigned j=0; j<s.size(); ++j) {
            s2 += s[i->at(j)];
         }
         orbits.back().insert(s2);
      }
   }

   std::vector<std::set<std::string> > orbits;
   std::set<std::vector<unsigned char> > induced;
   std::string mainorbit;
   unsigned mainorbit_size;
};

/* pairset encode/decode. The 2-element subsets under consideration are denoted by two-letter 
   pairs in ascending order, e.g. AB, CE, etc. Sometimes we would like to use a single character
   to refer to the 2-element subset, e.g AB=A, AC=B, AD=C, etc. So we have pairset_encode and 
   pairset_decode to go back and forth between these formats */
  
char pairset_encode[256];
char pairset_decode[512];

struct imgcfg_encoder {
   void add(const char *ie, unsigned mp) {
      unsigned char offset = ie[0] - 'A';
      offset *= nsetsize;
      offset += ie[1] - 'A';
      s += pairset_encode[offset];
      s += 'a' + mp;
   }
   std::string s;
};

/* all possible subsets of 1..n of order two, using letters so A=1, B=2, etc. */
std::set<std::string> pairsets;

/* for each subset of order two, make a bitmap corresponding to subsets which are disjoint,
   eg. AB has a vector of bits corresponding to CD CE DE... (Note that if we're solving the
   complementary problem, this will actually be a non-disjoint map) */
std::map<std::string, std::vector<unsigned> > disjointmap;

void make_pairsets(void) {
   char maxletter='A'+nsetsize-1;
   for(char ch1='A'; ch1 <maxletter; ++ch1) {
      for (char ch2=ch1+1; ch2 <=maxletter; ++ch2) {
         std::string s;
         s+=ch1;
         s+=ch2;
         pairsets.insert(s);
      }
   }
   /* for any pair AB, two bits are set corresponding to bits for A and B */
   std::map<std::string, unsigned> elembmap;

   /* for any pair AB, a bit is set to distinguish it from all other pairs */
   std::map<std::string, unsigned> pairbmap;

   char chnext = 'A';
   BOOST_FOREACH(const std::string &s, pairsets) {
      unsigned bmap = (1<<(s[0]-'A')) | (1<<(s[1]-'A'));
      elembmap[s] = bmap;
      unsigned xbit = (1 << pairbmap.size());
      pairbmap[s] = xbit;

      pairset_decode[2*(chnext-'A')] = s[0];
      pairset_decode[2*(chnext-'A')+1] = s[1];
      pairset_encode[ (s[0] - 'A') * nsetsize + (s[1] - 'A') ] = chnext++;
   }
   BOOST_FOREACH(const std::string &s1, pairsets) {
      BOOST_FOREACH(const std::string &s2, pairsets) {
         bool bdisjoint = ((elembmap[s1] & elembmap[s2]) == 0);
         if (bcomplementary) { /* if we're solving the complementary problem, we want pairs that are NOT disjoint */
            bdisjoint = !bdisjoint;
         }
         if (bdisjoint) {
            disjointmap[s1].push_back(pairbmap[s2]);
         }
      }
   }
}

/* suborbit walker: Call the suborbit walker through operator() giving the mainorbit
   in expanded form i.e. ("ABAC") and the size of the mainorbit. The suborbit walker
   will then call the walker object with each of the possible suborbits off of this
   main orbit */
template <typename walker>
struct suborbit_walker {
   suborbit_walker(walker &w_) : w(w_) { }
   void operator() (const std::string &sitem, unsigned orbit_size) {
      orbits_finder of(sitem);
      unsigned ssize = sitem.size() / 2;
      of.mainorbit_size = orbit_size;
      for (image_pattern_t::const_iterator j = image_by_orbit[ssize].begin();
            j != image_by_orbit[ssize].end(); ++j) {
         of.find_orbits(j->first);
         for (unsigned k=0; k<of.orbits.size(); ++k) {
            for (image_grouped_t::const_iterator ig = j->second.begin(); ig != j->second.end(); ++ig) {
               std::vector<unsigned> dp = decode_pattern(*ig);
               imgcfg_encoder icfg;
               for (unsigned seg = 0; seg < sitem.size(); seg += 2) {
                  icfg.add(&sitem[seg], dp[of.orbits[k].begin()->at(seg/2)-'a']);
               }
               w(icfg.s, of.mainorbit_size * of.orbits[k].size(), *ig);
            }
         }
      }
   }
   walker &w;
};

/* "main" orbits: orbits of 2-element subsets under permutation of the main set. First vector is for 
   number of non-unique elements in image, can be 1 through n/2. Second vector is for strings, which
   are representatives of the orbits of image sets of specified size, and then a string representing 
   the number of elements in the orbit. */
std::vector<std::vector<std::string> > orbits;

std::set<std::set<std::string> > prevorbits;

std::map<std::set<std::string>, unsigned> orbit_sizes;

unsigned imagesize = 0; /* to be incremented as we increase the size of image */

/* this is a consistency check on the orbits. The sum of all the orbit sizes of a specific size 
   must sum to a specific binomial and this procedure checks that */
void validate_orbits(void) {
   unsigned num = nsetsize * (nsetsize-1) / 2, denom=1;
   boost::uint64_t binom = 1;
   for (unsigned i=1; i<=nsetsize * (nsetsize-1) / 2 / 2; ++i) {
      boost::uint64_t sum = 0;
      for (unsigned j=i; j<orbits[i].size(); j+=(i+1)) {
         sum += boost::lexical_cast<unsigned>(orbits[i][j]);
      }
      binom *= num--; binom /= denom++;
      if (sum != binom) throw std::runtime_error("invalid orbits");
   }
}

/* for n=7 and higher it starts to take a while to compute the orbits, so they have been saved
   to a file (7orbit.txt and 8orbit.txt) where they don't need to be computed, instead they
   are just validated */
bool read_orbits_from_file(void) {
   std::string fname = boost::lexical_cast<std::string>(nsetsize) + "orbit.txt";
   std::ifstream ifs(fname.c_str());
   if (!ifs.good()) return false;
   for (;;) {
      char line[256];
      ifs.getline(line, sizeof(line)-1);
      if (ifs.eof()) {
         return true;
      }
      if (!ifs) throw std::runtime_error("bad " + fname);
      if (std::string(line).substr(0,6) == "Level ") {
         orbits.push_back(std::vector<std::string>());
         continue;
      }
      if (std::string(line).substr(0,4) == " AB ") {
         const char *p1 = line;
         while(*p1) {
            ++p1;
            const char *p2 = p1;
            while (*p2 != ' ' && *p2) ++p2;
            orbits.back().push_back(std::string(p1,p2));
            p1 = p2;
         }
      }
   }
   return true;
}

/* basically what we're going to do here is to take the previous level of orbits, add in one of
   the subsets AB, AC, etc. one by one, and permute it each time through all permutations to generate all
   of the orbit members , and then we remember the smallest representative and the size of the orbit for
   this member of the next level.
   The idea is that when we compute a image_configuration for a map image AB AC, we'll get 
   the same answer as if the map image was DE EF, so we're using symmetry to reduce the calculations.
   */
void next_image_orbit_level(void) {
   ++imagesize;
   std::set<std::set<std::string> > oldorbits = prevorbits;
   prevorbits.clear();
   while(!oldorbits.empty()){
      BOOST_FOREACH(const std::string &s, pairsets) {
         std::set<std::string> c = *oldorbits.begin();
         c.insert(s);
         if (c.size() != imagesize) continue;
         std::set<std::set<std::string> >sorter;
         /* make string of letters "ABCDE..." representing initial set 1...nsetsize */
         std::string permstring;
         for (unsigned i=0; i<nsetsize; ++i) {
            permstring.push_back('A'+i);
         }
         do {
            std::set<std::string> cc;
            BOOST_FOREACH(std::string s1, c) {
               s1[0] = permstring[s1[0]-'A'];
               s1[1] = permstring[s1[1]-'A'];
               if (s1[0] > s1[1]) std::swap(s1[0], s1[1]);
               cc.insert(s1);
            }
            sorter.insert(cc);
         } while(next_permutation(permstring.begin(), permstring.end()));
         prevorbits.insert(*sorter.begin());
         orbit_sizes[*sorter.begin()] = sorter.size();
      }
      oldorbits.erase(oldorbits.begin());
   }
}

void find_image_orbits(void) {
   /* put an empty placeholder for index zero which is unused in this scheme */
   orbits.resize(1);

   if (read_orbits_from_file()) {
      return;
   }

   /* prime the previous orbits with a null set to build upon */
   prevorbits.insert(std::set<std::string>());

   /* compute orbits for each possible image size. The final divide by two is because with no non-repeated
     elements in image it can only use at most half of the full image */
   for (unsigned i=0; i<nsetsize * (nsetsize-1) / 2 / 2; ++i) {
      std::cout << "Level " << i+1 << "\r" << std::flush;
      next_image_orbit_level();
      orbits.push_back(std::vector<std::string>());
      /* transform results from set<> format (sorted) to vector<> format (easier to access later) */
      for (std::set<std::set<std::string> >::const_iterator ip=prevorbits.begin(); ip != prevorbits.end(); ++ip) {
         for (std::set<std::string>::const_iterator is = ip->begin(); is != ip->end(); ++is) {
            orbits.back().push_back(*is);
         }
         unsigned orbit_size = orbit_sizes[*ip];
         if (orbit_size == 0) throw std::runtime_error("orbit_size was not computed in level " 
            + boost::lexical_cast<std::string>(orbits.size()));
         orbits.back().push_back(boost::lexical_cast<std::string>(orbit_size));
      }
   }
   std::cout << std::endl;
};

/* templated function to walk through all of the main orbits (on a specified number of items) and
   execute a callback for each */
template <typename walker>
void walk_main_orbits(walker &w, unsigned nitems) {
   const std::string *snext = &orbits[nitems].front();
   unsigned norbits = orbits[nitems].size() / (nitems + 1); /* the extra 1 is for the size */
   for (unsigned n=0; n<norbits; ++n) {
      std::string sitem;
      for (unsigned k=0; k<nitems; ++k) {
         sitem += *(snext++);
      }
      unsigned orbitsize = boost::lexical_cast<unsigned>(*(snext++));
      w(sitem, orbitsize, std::vector<unsigned>());
   }
}

/* precomputed domain bitsets for each image element. For every pair AB, find the bitmap consisting
   of all elements disjoint with it. If we are solving the complementary problem this wil be the
   set of all elements not disjoint */
std::vector<unsigned> fullbitset;

void make_domain_bitsets(void) {
   for (std::map<std::string, std::vector<unsigned> >::const_iterator i = disjointmap.begin(); i!= disjointmap.end(); ++i) {
      unsigned fullbitmap = 0;
      for (std::vector<unsigned>::const_iterator j=i->second.begin(); j != i->second.end(); ++j) {
         fullbitmap |= *j;
      }
      fullbitset.push_back(fullbitmap);
   }
}

/* suborbit_arranger: arrange the suborbits in such a way that each can be computed in one step from
   a suborbit that is already in the icfg_stack. First put each imgcfg (which is a representative of 
   a suborbit) in the stats map for its respective size. Then go through and try to link imgcfg values
   that are one step from each other into a directed graph. There are typically some imgcfg which are
   not reachable in one step from an existing imgcfg, so for that case add a "stepping stone" with an
   orbit size of zero so it won't factor into the results. Typically stepping stones are observed to be
   about 1% of the total image configurations. Once the graph is in place, traverse it in such a way
   that the image configurations are evaluated in sequences of single steps as planned.
   */
struct suborbit_arranger {

   void operator() (const std::string &imgcfg, unsigned orbitsize, const std::vector<unsigned> &multiplicities) {

      /* find the size of the mapping by adding up all of the multiplicities */
      unsigned size = 0;
      for (unsigned i=0; i< multiplicities.size(); ++i) {
         size += multiplicities[i];
      }
      /* add the image configuration to the necessary data structures */
      stats[size][imgcfg]=0;
      orbit_sizes[imgcfg] = orbitsize;
   }
   void process_tree(const std::string &orbit) {
      /* first run through check_dependencies, process and totalize values */
      check_dependencies(true);

      /* if stepping stones were needed during the dependency check, add them and check again
         to make sure the stepping stones did their job and connected all of the image
         configurations */
      if (all_stones.size()) {
         add_stones();
         clear_dependencies();
         check_dependencies(false);
         if (all_stones.size()) throw std::runtime_error("Cannot create stepping stones for " + orbit);
      }
      /* output the orbit */
      output();

      /* finished processing, clear the stats and start the next orbit */
      stats.clear();
      orbit_sizes.clear();
   }

   /* move the stepping stones to the stats container */
   void add_stones(void) {
      while(!all_stones.empty()) {
         std::string stone = *all_stones.begin();
         /* find the size of the stepping stone configuration, since the container segregates by size */
         unsigned size = 0;
         for (unsigned i=0; i<stone.size(); i+=2) {
            size += stone[i+1]-'a';
         }
         /* put it in the container with zero dependencies */
         stats[size][stone] = 0;

         /* set zero orbit size so the stepping stone doesn't contribute to the result */
         orbit_sizes[stone] = 0;
         all_stones.erase(all_stones.begin());
      }
   }

   /* clear all dependencies by walking through the stats container and resetting the count to zero */
   void clear_dependencies(void) {
      for (stats_t::iterator i=stats.begin(); i != stats.end(); ++i) {
         for (depcount_t::iterator j=i->second.begin(); j != i->second.end(); ++j) {
            j->second = 0;
         }
      }
   }

   /* check dependencies, by walking through all of the image configurations in this orbit and 
      incrementing the count for any other image confuration which can be reached in one step.
      At the end of this, any image configurations with a zero count cannot be reached in one
      step from another, and will need one or more stepping stones */

   void check_dependencies(bool btotalize) {
      /* go through all stats one by one */
      for (stats_t::iterator i=stats.begin(); i != stats.end(); ++i) {
         stats_t::iterator inext = i;
         if (++inext == stats.end()) break; /* get the pointer to the stats whose size is one higher */

         /* for each image configuration in the specified size... */
         for (depcount_t::const_iterator j=i->second.begin(); j != i->second.end(); ++j) {
            /* find the image configurations that can be reached in one step */
            for (unsigned k=0; k<j->first.size(); k+=2) {
               std::string stmp = j->first;
               ++stmp[k+1]; /* this is one step away from the image configuration pointed to by j */
               depcount_t::iterator di = inext->second.find(stmp); /* if the new image configuration exists...*/
               if (di != inext->second.end()) {
                  ++di->second; /*... then increment its reach count */
               }
            }
         }
      }

      /* make sure we start without any stones left over from previous runs */
      all_stones.clear();

      unsigned uncovered = 0;
      unsigned total = 0;
      /* go through all image configurations and find those that can't be reached in one step */
      for (stats_t::iterator i=stats.begin(); i != stats.end(); ++i) {
         if (i == stats.begin()) continue;
         for (depcount_t::const_iterator j=i->second.begin(); j != i->second.end(); ++j) {
            ++total;
            if (j->second == 0) { /* if this image configuration can't be reached in one step... */
               std::vector<std::string> stones;
               find_stepping_stones(j->first, stones); /* get stepping stones for it */
               if (stones.empty()) throw std::runtime_error("no stepping stone for " + j->first);
               for(unsigned i=0; i<stones.size(); ++i) { /* maintain a container of all stepping stones for later insertion */
                  all_stones.insert(stones[i]);
               }
            }
         }
      }
      uncovered += all_stones.size();
   }

   /* find stepping stones for an image configuration which currently has no sequence of single steps to reach it */
   std::vector<std::string> find_stepping_stones(const std::string &s, std::vector<std::string> &res) {
      res.clear();
      /* find size of the stepping stone */
      unsigned size = 0;
      for (unsigned i=0; i<s.size(); i+=2) {
         size += s[i+1]-'a';
      }
      /* start with two steps behind the stepping stone and keep going further back if necessary */
      for (unsigned backup=2; ;++backup) {
         stats_t::const_iterator i=stats.find(size - backup);
         if (i == stats.end()) { /* if we backed all the way to the beginning and still couldn't find, this shouldn't happen */
            res.clear();
            return res;
         }
         /* go through image configurations in the specified size and see if any can be a stepping stone
            to the given item */
         for (depcount_t::const_iterator j=i->second.begin(); j != i->second.end(); ++j) {
            bool bvalid = true;
            std::map<unsigned, unsigned> posvector;

            /* go through the counts */
            for (unsigned i=0; i<s.size(); i+=2) {
               int diff = s[i+1]-j->first[i+1]; 
               if (diff < 0) { /* in order to reach "s" from "j->first" by incrementing, none of j->first counts may be greater */
                  bvalid = false;
                  break;
               }
               if (diff > 0) { /* make a list of positions that need to be incremented, and how many times */
                  posvector[i+1] = (unsigned) diff;
               }
            }

            /* if none of the counts were negative, that means "s" can be reached from "j->first" */
            if (bvalid) {
               std::string step = j->first;
               unsigned nsteps = 0;
               res.clear();
               /* generate a sequence of steps to reach s from j->first */
               for(;;) {
                  if (nsteps+1 == backup) { /* required number of steps has been made, return successfully */
                     return res;
                  }
                  if (posvector.empty()) { /* no more steps available, shouldn't happen but return unsuccessfully if it does */
                     res.clear();
                     return res;
                  }
                  /* use the first available differing string position */
                  unsigned pos = posvector.begin()->first;
                  ++step[pos]; /* generate a single step at the noted position and push the stepping stone onto the results list */
                  res.push_back(step);
                  /* decrease the number of steps available at the noted position. If this is exhausted, remove ot
                  from the list so that other positions become available */
                  if (--posvector[pos] == 0) posvector.erase(posvector.begin());

                  ++nsteps; /* one step closer to finishing */
               }
            }
         }
      }
   }
   /* output the image configurations by creating a directed graph and traversing it. This will
      result in a list of image configurations in order so that new nodes are one step
      ahead of a node on the path from the root to the current node */
   void output(void) {
      if (stats.empty()) return; /* make it work for n<5 */
      std::set<std::string> inlinks; /* directed graph edges going into the nodes */
      std::set<std::string> outlinks; /* directed graph edges going out of the nodes */

      /* walk through the stats container and make the directed graph */
      for (stats_t::iterator i=stats.begin(); i != stats.end(); ++i) {
         stats_t::iterator inext = i;
         if (++inext == stats.end()) break;
         for (depcount_t::const_iterator j=i->second.begin(); j != i->second.end(); ++j) {
            for (unsigned k=0; k<j->first.size(); k+=2) {
               std::string stmp = j->first;
               ++stmp[k+1];
               depcount_t::iterator di = inext->second.find(stmp);
               /* if there is a link between stmp and *di, then insert the edge to both inlinks and outlinks */
               if (di != inext->second.end()) {
                  inlinks.insert(stmp + j->first);
                  outlinks.insert(j->first + stmp);
               }
            }
         }
      }

      /* edges of the directed graph have been constructed. Now walk the graph from the root to the extreme
         nodes, removing nodes and edges as they are processed */
      unsigned startlevel = icfg_stack.size();

      /* open file if we are writing results to file */
      std::string orbitname;
      for (unsigned i=0; i<icfg_stack.back().name.size(); ++i) {
         orbitname += std::string(pairset_decode + 2*(icfg_stack.back().name[i] - 'A'), 2);
      }

      /* we use different naming conventions here than in the mainorbit so save name to restore later */
      std::string namesave = stats.begin()->second.begin()->first;
      namesave.swap(icfg_stack.back().name);

      for (;;) {
         /* are there any links going out of the current node ? */
         bool b_links_out = false;
         std::set<std::string>::iterator io = outlinks.lower_bound(icfg_stack.back().name);
         if (io != outlinks.end() && icfg_stack.back().name == io->substr(0, icfg_stack.back().name.size())) {
            b_links_out = true;
         }

         /* are there any links going out of the current node ? */
         while (b_links_out) {
            /* if so then push back the first such link and continue back to the top of the loop to process it */
            unsigned namesize = icfg_stack.back().name.size();
            icfg_stack.push_back(icfg_stack_t(icfg_stack.back().nbits+1));
            icfg_stack.back().name = io->substr(namesize);

            b_links_out = false;
            io = outlinks.lower_bound(icfg_stack.back().name);
            if (io != outlinks.end() && icfg_stack.back().name == io->substr(0, icfg_stack.back().name.size())) {
               b_links_out = true;
            }

            icfg_stack_t &penultimate = *(++icfg_stack.rbegin());
            boost::uint64_t res = 0;
            std::string sname;
            /* find the position to increment */
            const std::string &s1 = icfg_stack.back().name;
            const std::string &s2 = penultimate.name;
            for (unsigned i=1; i<s1.size(); i+=2) {
               if (s1[i] != s2[i]) {
                  res = icfg_stack.back().next_level(penultimate, fullbitset[s2[i-1]-'A']);
                  icfg_stack.back().divisor = s1[i] - 'a';
                  break;
               }
            }
            sname = icfg_stack.back().name;
            res /= icfg_stack.back().divisor;
            multiprecision mtmp = res;
            mtmp *= orbit_sizes[sname];
            std::vector<unsigned> multiplicities;
            unsigned size = 0;
            for (unsigned i=0; i<sname.size(); i+= 2) {
               multiplicities.push_back(sname[i+1]-'a');
               size += multiplicities.back();
            }
            std::sort(multiplicities.begin(), multiplicities.end(),std::greater<unsigned>());
            results_by_size[size][multiplicities] += mtmp;
         }

         /* there are no more links coming out of the current node. It has been completely processed so
            delete all links going into the current node, and then pop it from the stack */
         for(;;) {
            std::set<std::string>::iterator ii = inlinks.lower_bound(icfg_stack.back().name);
            if (ii == inlinks.end()) break;
            if (icfg_stack.back().name != ii->substr(0, icfg_stack.back().name.size())) break;

            /* links come in pairs, erase the outlink version and the inlink version */
            outlinks.erase(ii->substr(icfg_stack.back().name.size()) + icfg_stack.back().name);
            inlinks.erase(ii);
         }
         if (icfg_stack.size() == startlevel) {
            icfg_stack.back().name.swap(namesave);
            break; /* when we complete the traversal, the stack will be where we started */
         }
         icfg_stack.pop_back();
      }
   }
   typedef std::map<std::string, unsigned> depcount_t;
   typedef std::map<unsigned, depcount_t> stats_t;
   std::set<std::string> all_stones;
   stats_t stats;
   std::map<std::string, unsigned> orbit_sizes;
};

/* mainorbit_arranger: arrange the mainorbits in such a way that the starting image configuration
   for each mainorbit can be computed by adding just one more element to the image of an image configuration
   which is already on the stack */
class mainorbit_arranger {
public:
   typedef std::map<std::set<char>, unsigned> orbitm_t;
   typedef std::map<unsigned, orbitm_t> statsm_t;

   /* operator() will be called for each main orbit (imgcfg) and we will just translate and save the string 
      until we have them all */
   void operator() (const std::string &imgcfg, unsigned orbitsize, const std::vector<unsigned> &multiplicities) {
      std::set<char> newstr;
      std::string oldstr = imgcfg;
      while (!oldstr.empty()) {
         newstr.insert(pairset_encode[ (oldstr[0] - 'A') * nsetsize + (oldstr[1] - 'A') ]);
         oldstr = oldstr.substr(2);
      }
      m[newstr.size()][newstr] = 0;
      orbit_sizes[imgcfg] = orbitsize;
   }

   /* once all of the mainorbits have been added, they can be processed. */
   void process(void) {
      for (statsm_t::iterator i=m.begin(); i != m.end(); ++i) {
         statsm_t::iterator inext = i;
         if (++inext == m.end()) break;
         for (orbitm_t::iterator j1 = i->second.begin(); j1 != i->second.end(); ++j1) {
            for (orbitm_t::iterator j2 = inext->second.begin(); j2 != inext->second.end(); ++j2) {
               std::set<char> cs2 = j2->first;
               for (std::set<char>::const_iterator k=j1->first.begin(); k != j1->first.end(); ++k) {
                  cs2.erase(*k);
               }
               if (cs2.size() == 1) {
                  ++j2->second;
                  std::string inlink, outlink;
                  for (std::set<char>::const_iterator k=j1->first.begin(); k != j1->first.end(); ++k) {
                     outlink += *k;
                  }
                  for (std::set<char>::const_iterator k=j2->first.begin(); k != j2->first.end(); ++k) {
                     inlink += *k;
                  }
                  outlink += '-'; inlink += '-';
                  for (std::set<char>::const_iterator k=j1->first.begin(); k != j1->first.end(); ++k) {
                     inlink += *k;
                  }
                  for (std::set<char>::const_iterator k=j2->first.begin(); k != j2->first.end(); ++k) {
                     outlink += *k;
                  }
                  inlinks.insert(inlink);
                  outlinks.insert(outlink);
               }
            }
         }
      }
      for (statsm_t::iterator i=m.begin(); i != m.end(); ++i) {
         if (i == m.begin()) continue;
         for (orbitm_t::iterator j1 = i->second.begin(); j1 != i->second.end(); ++j1) {
            if (j1->second == 0) throw std::runtime_error("missing link in orbits");
         }
      }
      icfg_stack.push_back(icfg_stack_t(0));
      icfg_stack.back()[0] = 1;
      icfg_stack.push_back(icfg_stack_t(2));
      icfg_stack.back().name = "A";
      unsigned prevlevel = 1; /* so we only output nodes when they are reached the first time */
      time_t starttm = time(NULL);
      unsigned nprocessed = 0;
      for (;;) {
         if (icfg_stack.size() == 1) break; /* when we complete the traversal, the stack will have just the initializer */

         /* are there any links going out of the current node? If so set pos to a valid position */
         std::set<std::string>::iterator io = outlinks.lower_bound(icfg_stack.back().name);
         std::string::size_type pos = std::string::npos;
         if (io != outlinks.end()) pos = io->find('-');
         if (pos != std::string::npos && icfg_stack.back().name != io->substr(0, pos)) {
            pos = std::string::npos;
         }

         if (icfg_stack.size() > prevlevel) { /* if we're reaching a node from above, we're visiting it for
                                             the first time and should output on this condition only */
            icfg_stack_t tmp(icfg_stack.back().nbits - 1);
            char ch = leveldiff();
            unsigned bitset = fullbitset.empty() ? 0 : fullbitset[ch-'A'];
            tmp.next_level(*(++icfg_stack.rbegin()), bitset);
            icfg_stack.back().divisor = 2;
            boost::uint64_t res = icfg_stack.back().next_level(tmp, bitset);
            {
               std::string orbitname;
               for (unsigned i=0; i<icfg_stack.back().name.size(); ++i) {
                  orbitname += std::string(pairset_decode + 2*(icfg_stack.back().name[i] - 'A'), 2);
               }
               std::cout << icfg_stack.back().name << " " << orbitname << std::endl;

               /* before doing suborbits, write out the result for the main orbit, it's just
                  the image configuration that has the multiplicity value 2 for every image element */
               boost::uint64_t res = icfg_stack.back().res / icfg_stack.back().divisor;
               multiprecision mtmp = res;
               mtmp *= orbit_sizes[orbitname];
               std::vector<unsigned> multiplicities(orbitname.size()/2, 2);
               results_by_size[orbitname.size()][multiplicities] += mtmp;

               suborbit_arranger ct;
               suborbit_walker<suborbit_arranger> swk(ct);
               swk(orbitname, orbit_sizes[orbitname]);
               ct.process_tree(orbitname);
            }
         }
         prevlevel = icfg_stack.size();

         /* are there any links going out of the current node ? */
         if (pos != std::string::npos) {
            if (icfg_stack.back().name == io->substr(0, pos)) {
               /* if so then push back the first such link and continue back to the top of the loop to process it */
               icfg_stack.push_back(icfg_stack_t(icfg_stack.back().nbits+2));
               icfg_stack.back().name = (io->substr(pos+1));
               continue;
            }
         }

         /* there are no more links coming out of the current node. It has been completely processed so
            delete all links going into the current node, and then pop it from the stack */
         for(;;) {
            std::set<std::string>::iterator ii = inlinks.lower_bound(icfg_stack.back().name);
            if (ii == inlinks.end()) break;
            std::string::size_type pos = ii->find('-');
            
            if (icfg_stack.back().name != ii->substr(0, pos)) break;

            /* links come in pairs, erase the outlink version and the inlink version */
            outlinks.erase(ii->substr(pos+1) + "-" + icfg_stack.back().name);
            inlinks.erase(ii);
         }
         icfg_stack.pop_back();
      }
      std::cout << std::endl << "Elapsed: " << time(NULL) - starttm << std::endl;
   }
   char leveldiff(unsigned level) const {
      const icfg_stack_t &s1 = icfg_stack[level];
      const icfg_stack_t &s2 = icfg_stack[level+1];
      for (unsigned i=0; i<s2.name.size(); ++i) {
         if (s1.name.find(s2.name[i]) == std::string::npos) {
            return s2.name[i];
         }
      }
      throw std::runtime_error("leveldiff not found for level");
   }
   char leveldiff(void) const {
      if (icfg_stack.size() < 2) return icfg_stack.back().name[0];
      for (unsigned i=0; i<icfg_stack.back().name.size(); ++i) {
         if ((++icfg_stack.rbegin())->name.find(icfg_stack.back().name[i]) == std::string::npos) {
            return icfg_stack.back().name[i];
         }
      }
      throw std::runtime_error("leveldiff not found");
   }
   statsm_t m;
   std::set<std::string> inlinks; /* directed graph edges going into the nodes */
   std::set<std::string> outlinks; /* directed graph edges going out of the nodes */
   std::map<std::string, unsigned> orbit_sizes;
};

void solve_image_configurations(void) {
   find_map_patterns();
   mainorbit_arranger s;
   for (unsigned i=1; i<=(nsetsize * (nsetsize-1) / 4); ++i) {
      walk_main_orbits(s, i);
   }
   s.process();
}

/* the net value to inclusion exclusion from a fully-multiple mapping.
   If all of the possible unions of base mappings which form a specific fully-multiple mapping
   are enumerated, and the net value to inclusion exclusion is determined (i.e. minus pairwise, plus 
   3-wise, minus 4-wise, etc. etc.) then it's a very complicated situation, but it simplifies greatly 
   via a formula. It's simply the product of each multiplicity reduced by 1, times -1 for each of the 
   even multiplicities.
   */
int value_function(const std::vector<unsigned> & item) {
   int value = 1;
   for (unsigned i=0; i<item.size(); ++i) {
      int x = item[i] -1;
      if (x&1) x=-x;
      value *= x;
   }
   return value;
}

/* here is the final stage of the problem. We've computed the results of all image_configurations,
   and used them to compute the numbers of mappings satisfying the required image multiplicity criteria.
   Now we have to use these to compute the top level of inclusion-exclusion coefficients, which get
   multiplied by factorials for the final result. */
void compute_final_result(void) {
   unsigned nelements = nsetsize * (nsetsize-1) /2; /* number of two-element subsets, n choose 2 */
   unsigned ndisjoint = (nsetsize -2) * (nsetsize-3) /2; /* number of elements disjoint from any given, n-2 choose 2 */
   if (bcomplementary) {
      ndisjoint = nelements - ndisjoint; /* we want the non-disjoint elements for the complementary problem */
   }

   /* calculate a vector of factorials from zero factorial to nelements factorial */
   std::vector<multiprecision> factorial;
   factorial.push_back(1);
   for (unsigned i=1; i<=nelements; ++i) {
      factorial.push_back(factorial.back());
      factorial.back() *= i;
   }

   multiprecision coeff = 1; /* the current coefficient for the current factorial */
   unsigned num = nelements, denom = 1; /* numerator and denominator for calculating sequential combinations */

   /* first inclusion/exclusion term is 1 * nelements! */
   std::cout << coeff << " * " << factorial.back() << std::endl;

   /* coefficient gets multiplied by factorial and added to the problem_solution */
   multiprecision problem_solution = coeff * factorial.back();
   factorial.pop_back();

   std::vector<multiprecision> carryforward;
   for (unsigned i=1; i<=nelements; ++i) {
      /* For this problem, every time we solve an inclusion-exclusion term, some of the items happen to
         be carried forward but multiplied by an ndisjoint term and the next in a series of combinations.
         This loop maintains these carryforwards so we don't have to start over with them each time */
      for (unsigned j=0; j<carryforward.size(); ++j) {
         carryforward[j] *= num;
         carryforward[j] /= (denom - j - 1);
         carryforward[j] *= ndisjoint;
      }

      /* The main coeffient increases this way for each inclusion exclusion step. It's basically the 
      next highest power of ndisjoint followed by the next combination described by num and denom */
      coeff *= num--;
      coeff /= denom++;
      coeff *= ndisjoint;

      /* now the new values which will be any of the net contributions of any tallied maptypes whose size
         matches the current level */
      multiprecision newvalues = 0;
      std::map<unsigned, std::map<std::vector<unsigned>, multiprecision> >::const_iterator im = results_by_size.find(i);
      if (im != results_by_size.end()) {
         for(std::map<std::vector<unsigned>, multiprecision>::const_iterator j = im->second.begin(); j != im->second.end(); ++j) {
            multiprecision mpnet = j->second;
            mpnet *= value_function(j->first);
            newvalues += mpnet;
         }
      }
      carryforward.push_back(newvalues);

      /* now add in the main value for this coefficient.. */
      multiprecision thiscoeff = coeff;

      /* and the values carried forward from previous levels */
      for (unsigned j=0; j<carryforward.size(); ++j) {
         thiscoeff += carryforward[j];
      }
      /* and a +/- since inclusion/exclusion alternates signs of corrections */
      std::cout << ((i&1) ? '-' : '+') << thiscoeff << " * " << factorial.back() << " " ;

      /* now multiply the coefficient by the factorial and appropriate sign, and accumulate it into 
      the problem solution */
      multiprecision thisloop = factorial.back() * thiscoeff;
      factorial.pop_back();
      if (i&1) thisloop = -thisloop;
      std::cout << "( " << thisloop << " )" << std::endl;
      problem_solution += thisloop;
   }
   /* this is it. All coefficients and factorials have been multiplied and totalled, so here is the result. */
   std::cout << problem_solution << std::endl;
}

void usage(void) {
   throw std::runtime_error("usage: subsetperms nsetsize [c]\n"\
   "   where nsetsize is from 5 through 8\n" \
   "   c solves the complementary problem\n");
}

int main(int argc, char *argv[]) {
   try {
      if (argc <2) usage();
      for (int i=1; i<argc; ++i) {
         if (argv[i][0] == 'c') bcomplementary = true;
         else try {
            nsetsize = boost::lexical_cast<unsigned>(argv[i]);
            nsubsets = nsetsize * (nsetsize-1) / 2;
         } catch(...) {
            usage();
         }
      }
      std::cout << "determining 2-element subsets" << std::endl;
      make_pairsets();

      std::cout << "constructing Pascal's triangle for ranking bit-permutations" << std::endl;
      make_pascal_triangle();

      std::cout << "preallocating memory for evaluating image configurations" << std::endl;
      make_icfg_memory();

      std::cout << "enumerating fully-multiple map types" << std::endl;
      enumerate_fully_multiple_map_types();
      std::cout << "found " << maptypes.size() << " maptypes" << std::endl;

      {
         std::cout << "finding orbits for image multiplicity sets" << std::endl;
         time_t elapsed = time(NULL);
         find_image_orbits();
         elapsed = time(NULL) - elapsed;
         std::cout << elapsed << " seconds" << std::endl;
         validate_orbits();
      }

      std::cout << "precomputing domain bitsets for image elements" << std::endl;
      make_domain_bitsets();

      std::cout << "solving image configurations in optimized order" << std::endl;
      if (nsetsize > 2) {
         solve_image_configurations();
      }

      std::cout << "computing final result" << std::endl;
      compute_final_result();

   } catch (std::exception &x) {
      std::cout << std::endl << x.what() << std::endl;
      return 1;
   }
   return 0;
}
