/*
   Program by Ronald Niles to solve the following problem:
   (C) 2017 Ronald S Niles, GPL 3.0 License

   OEIS Sequence A244493, alternate form (James East 2/17/2017)
      Let X be the set of all 2-element subsets of {1,...,n}.  
      How many permutations f of X are there such that for any A in X, f(A) is not disjoint from A?

   Using several levels of the inclusion-exclusion principle, this problem breaks down into a 
   large number of image_configurations that are faster to solve on a computer.

   Instead of 1..n we use ABC.. so that two-element subsets can be denoted as AB AC BC etc. 
   and are readily distinguished from numerals.

   For details on the mathematical formulas and algorithms that this program is based on,
   please see the A244493.pdf document.
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
#include <boost/multiprecision/cpp_int.hpp>
typedef boost::multiprecision::int256_t multiprecision;

#include "btree_map.h"
bool bverbose = false; /* flag to print out extra information */
bool bcomplementary = false; /* flag to solve the complementary problem */

/* the initial set 1...n, specify n as "nsetsize" */
unsigned nsetsize;

/* image_configurations - each string describes a state of map images for which we have to compute
   how many times they can occur*/
std::set<std::string> image_configurations;
std::map<std::string, boost::uint64_t> solved_image_configurations;

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
  given a vector of multiplicities, this will provide a pattern based on
  small letters of the alphabet showing the number of times each
  multiplicity value appears
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
   runs nondescending), and put them in the image_by_orbit list.
*/
void find_map_patterns(void) {
   for (std::set<std::vector<unsigned> >::const_iterator i=maptypes.begin(); i != maptypes.end(); ++i)
   {
      std::string s = map_pattern(*i);
      if (s.size() != i->size()) throw std::runtime_error("size mismatch in generating patterns");
      image_by_orbit[s.size()][s].push_back(*i);
   }
}

/* orbits finder object. Start with the mainorbit, which is based on the subset of elements in
   a map image without regards to multiplicity. The purpose of this class is to find
   orbits which are based on the original main orbit but include multiplicities, in other words
   if the orbit is {AB AC BC}, and the multiplicities are {2 3 4}, each permutation of the
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


/* templated functor icf_walker which will be called with a mainorbit string and go through all
   of the map_patterns in the image_by_orbit and call back the function "w" with a representative
   of all the new orbits found by the orbits_finder */
template <typename walker>
struct icf_walker {
   icf_walker(walker w_) : w(w_) { }
   void operator() (const std::string &sitem, unsigned size, const std::vector<unsigned> multiplicities) {
      orbits_finder of(sitem);
      of.mainorbit_size = size;
      for (image_pattern_t::const_iterator j = image_by_orbit.begin()->second.begin();
            j != image_by_orbit.begin()->second.end(); ++j) {
         of.find_orbits(j->first);
         for (unsigned k=0; k<of.orbits.size(); ++k) {
            for (image_grouped_t::const_iterator ig = j->second.begin(); ig != j->second.end(); ++ig) {
               std::vector<unsigned> dp = decode_pattern(*ig);
               std::string subproblem;
               for (unsigned seg = 0; seg < sitem.size(); seg += 2) {
                  subproblem += sitem.substr(seg, 2);
                  std::string snumber = boost::lexical_cast<std::string>(dp[of.orbits[k].begin()->at(seg/2)-'a']);
                  while (snumber.size() < 2) snumber.insert(snumber.begin(), '0');
                  subproblem.append(snumber);
               }
               w(subproblem, of.mainorbit_size * of.orbits[k].size(), *ig);
            }
         }
      }
   }
   walker w;
};

/* templated functor to walk through all orbits of all map patterns for the purpose
  of generating image_configurations to evaluate, or later on looking up
  the solved image_configurations to tabulate */
template <typename walker>
void walk_image_configurations(walker w) {
   find_map_patterns();
   while(!image_by_orbit.empty()) {
      unsigned ncolumns = image_by_orbit.begin()->first;
      walk_main_orbits(icf_walker<walker>(w), ncolumns);
      image_by_orbit.erase(image_by_orbit.begin());
   }
}


/* all possible subsets of 1..n of order two, using letters so A=1, B=2, etc. */
std::set<std::string> pairsets;

/* for each subset of order two, make a bitmap corresponding to subsets which are disjoint,
   eg. AB has a vector of bits corresponding to CD CE DE... */
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

   BOOST_FOREACH(const std::string &s, pairsets) {
      unsigned bmap = (1<<(s[0]-'A')) | (1<<(s[1]-'A'));
      elembmap[s] = bmap;
      pairbmap[s] = (1 << pairbmap.size());
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
   if (bverbose) {
      std::cout << "image pairsets (" << pairsets.size() << "): ";
      for (std::set<std::string>::const_iterator i=pairsets.begin(); i!=pairsets.end(); ++i) {
         std::cout << *i << " ";
      }
      std::cout << std::endl;
   }
}

/* orbits of image sets of subsets under permutation. First vector is for number of non-unique elements
  in image, can be 1 through n/2. Second vector is for strings, which are representatives of the orbits
  of image sets of specified size, and then a string representing the number of elements in the orbit. */
std::vector<std::vector<std::string> > orbits;

std::set<std::set<std::string> > prevorbits;

std::map<std::set<std::string>, unsigned> orbit_sizes;

unsigned imagesize = 0; /* to be incremented as we increase the size of image */

void validate_orbits(void) {
   if (bverbose) std::cout << "orbit validation data: " << std::endl;
   unsigned num = nsetsize * (nsetsize-1) / 2, denom=1, binom = 1;
   for (unsigned i=1; i<=nsetsize * (nsetsize-1) / 2 / 2; ++i) {
      unsigned sum = 0;
      if (bverbose) std::cout << orbits[i].size() / (i+1) << " ";
      for (unsigned j=i; j<orbits[i].size(); j+=(i+1)) {
         sum += boost::lexical_cast<unsigned>(orbits[i][j]);
      }
      binom *= num--; binom /= denom++;
      if (bverbose) std::cout << sum << " " << binom << std::endl;
      if (sum != binom) throw std::runtime_error("invalid orbits");
   }
}

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
void walk_main_orbits(walker w, unsigned nitems) {
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

/* precomputed bitmaps. For every pair AB, and every number of column partners, 
   compute a vector of bitmaps corresponding to all possible combinations */
std::map<std::string, std::map<unsigned, std::vector<unsigned> > > precomputed;


/* compute bitmaps for all combinations of n elements in bits vector */
/* so for example, AB can be mapped to by any other disjoint two element subset, i.e. BC, BD, CD, ...
   Since we're dealing with mappings that can be many to one, we assign a bit to each two-element subset.
   The bit represents that subset as mapping to AB in the map under consideration.
   For example if we want to go through all of the possiblities for having 3 subsets mapping to AB, 
   we go to precomputed["AB"][3] and this is a vector of bitmaps where each bitmap has three bits set
   corresponding to the various combinations of three subsets that are all disjoint from AB.
   */
void precompute_domain_bitmaps(std::vector<unsigned> &res, const std::vector<unsigned> bits, unsigned n) {
   std::vector<unsigned> combi;
   for(unsigned i=0; i<n; ++i) combi.push_back(i);
   for(;;) {
      unsigned bmap = 0;
      BOOST_FOREACH(unsigned x, combi) {
         bmap |= bits[x];
      }
      res.push_back(bmap);
      if (combi.back() < bits.size()-1) {
         ++combi.back();
         continue;
      }
      unsigned p1=n-1, p2=bits.size()-1;
      while(combi[p1] == p2) {
         if (p1 == 0) return;
         --p1;
         --p2;
      }
      p2 = ++combi[p1++];
      while(p1 < combi.size()) {
         combi[p1++] = ++p2;
      }
   }
}

void make_domain_table(void) {
   for (std::map<std::string, std::vector<unsigned> >::const_iterator i = disjointmap.begin(); i!= disjointmap.end(); ++i) {
      for (unsigned j=2; j<=i->second.size(); ++j) {
         precompute_domain_bitmaps(precomputed[i->first][j], i->second, j);
      }
   }
}

/* enumerate_image_configurations. This is done by using the "insert_image_config" callback 
   which gets walked by the "walk_image_configurations" templated function */
struct insert_image_config {
   void operator() (const std::string &imgcfg, unsigned orbitsize, const std::vector<unsigned> &multiplicities) {
      /* The orbits and permuted maptypes have been combined by interlacing two letters (for the image element) 
         with two digits (for the multiplicity) for a string e.g. "AB02AC04AD03" */
      image_configurations.insert(imgcfg);
   }
};
void enumerate_image_configurations(void) {
   walk_image_configurations(insert_image_config());
}

boost::uint64_t max_image_configuration_val = 0;

/* solving the image_configurations. A image_configuration is represented as a string for instance:
   AB03AC02BD05EF03
   This string means, 
      "how many one-to-many mappings "f(x)" of {AB, AC, BC, AD, BD, CD, AE, BE, CE, DE...} to itself
          (use whatever set of two-element subsets is appropriate for your given "n")
      are possible where f(x) is disjoint from (x), and
        3 elements map to AB, 2 elements map to AC, 5 elements map to BD, and 3 elements map to EF" 
        ( and no other elements are mapped to)

   Since these are fully-multiple mappings, each element will be mapped to at least twice.

The idea is to solve the image_configurations using bitmaps. Since the map is one to many, 
once an item is used in the domain, it can't be used again and a bitmap is used to represent which
items in the domain have been used. 

In order to piggyback the solutions, we solve them in sorted order. For example, since 
   AB03AC02BD06EF03
   AB03AC02BD06EF04
will be solved sequentially, the state information for AB03AC02BD06 is popped from the stack between these
two operations so that we only have to solve the last stage of the problem again.

Also, the solutions are pigeonholed via the std::map<unsigned, boost::uint64_t> . There are in many cases
far more solutions than there are possible bitmaps of the intermediate stages. For example for n=7
there are often billions of solutions to a image_configuration but there are only 21 choose n possibilites
for a bitmap with n bits and this maxxes out around 300,00-400,000, so we can pigeonhole the intermediate 
stages that correspond to the same bitmap and drastically reduce the number of cases to examine.

*/

/* this is using the google btree map for better performance and memory utilization */
typedef btree::btree_map<unsigned, boost::uint64_t> bm_map_t;

void add_next_vector(bm_map_t &mx, 
                     const bm_map_t &m1,
                     const std::vector<unsigned> &v1)
{
   mx.clear();
   /* go through the existing level of bitmaps */
   for(bm_map_t::const_iterator i = m1.begin(); i != m1.end(); ++i) {
      /* add the new bitmaps from the vector */
      for(unsigned j = 0; j< v1.size(); ++j) {
         if ((i->first & v1[j]) == 0) /* if the bitmaps have no bits in common... */
         {
            /* then they can be combined to go to the next level of the mapping */
            boost::uint64_t v = (mx[i->first | v1[j]] += i->second);
            /* keep track of the maximum number encountered, so we can be sure we don't exceed
            size limitations on the 64-bit integer used */
            if (v > max_image_configuration_val) max_image_configuration_val = v;
         }
      }
   }
}

/* this item is so we can push/pop a stack of partial image_configuration results so we can piggyback
   common results from one image_configuration to the next */
class seqstack_t {
public:
   bm_map_t m1;
   std::string name;
};

void solve_image_configurations(void) {
   /* keep track of time spent solving the image_configurations. */
   time_t start = time(NULL);
   std::vector<seqstack_t> vs;
   {
      /* initialize stack with special backstop item designed to work when the first vector is added */
      seqstack_t init;
      init.m1[0] = 1;
      vs.push_back(init);
   }

   /* copy original number of image_configurations because we will delete items from 
      the set of image_configurations as they are solved */
   const unsigned nproblems = image_configurations.size();

   unsigned neval = 0;

   /* write the results of the image_configuration evaluations to a file for later reference */
   std::string fname = "subproblems";
   fname += boost::lexical_cast<std::string>(nsetsize);
   fname += ".txt";
   std::ofstream ofs(fname.c_str());

   /* solve each image_configuration in order */
   while (!image_configurations.empty()) {
      /* copy the first remaining image_configuration and then erase it from the set */
      std::string image_configuration = *image_configurations.begin();
      image_configurations.erase(image_configurations.begin());

      /* piggyback on results of previous problem if possible: 
         pop the stack back to the point where the partial previous problem is 
         identical to the first steps of the current problem, then we've saved some work */
      while (vs.back().name != image_configuration.substr(0, vs.back().name.size())) {
         vs.pop_back();
      }

      /* for the remaining stages, do them step by step. */
      while(vs.back().name != image_configuration) {

         /* four characters at a time, specifying the image element and the number
            of domain elements that map to it */
         std::string s = image_configuration.substr(vs.back().name.size(), 4);
         if (s.size() != 4) throw std::runtime_error("image_configurations string error");
         unsigned nelements = boost::lexical_cast<unsigned>(s.substr(2, 2));

         /* get the precomputed vector containing all bitmaps corresponding to all 
          "nelements choose 2" combinations of domain elements which are disjoint from 
          the specified image element */
         std::vector<unsigned> &vcol = precomputed[s.substr(0,2)][nelements];
         if (vcol.empty()) throw std::runtime_error("precomputed bitmap vector not found");

         /* send the vector and the previous level map to the routine that will check and add
         the new bitmaps */
         seqstack_t next;
         add_next_vector(next.m1, vs.back().m1, vcol);

         /* then update the name for the new level we did, and push it on the stack */
         next.name = vs.back().name + s;
         vs.push_back(next);
      }

      /* When we get here, we've evaluated the entire image_configuration, so we can add up the values 
         at the end of the stack to get how many mappings satisfied all of the problem
         constraints */
      boost::uint64_t res = 0;
      for(bm_map_t::const_iterator i = vs.back().m1.begin(); i != vs.back().m1.end(); ++i) {
         res += i->second;
      }
      /* save the result of this image_configuration */
      solved_image_configurations[image_configuration] = res;

      /* Keep track of the maximum value to make sure we're not getting close to 64-bit integer size limitations */
      if (res > max_image_configuration_val) max_image_configuration_val = res;

      /* also, write each result to the output file for later reference purposes */
      ofs << vs.back().name << "," << res << std::endl;

      /* every 100 entries, print out time and progress statistics */
      if ((++neval % 100) == 0) {
         unsigned nbits = 0;
         boost::uint64_t tmp = max_image_configuration_val;
         while(tmp) {
            ++nbits;
            tmp >>= 1;
         }
         std::cout << neval << "/" << nproblems << " elapsed: " << time(NULL) - start << " largest value: " << max_image_configuration_val << " (" << nbits << " bits)\r" << std::flush;
      }
   }
   /* at the end print out largest values encountered during the process */
   {
      unsigned nbits = 0;
      boost::uint64_t tmp = max_image_configuration_val;
      while(tmp) {
         ++nbits;
         tmp >>= 1;
      }
      std::cout << std::endl << " largest value encountered: " << max_image_configuration_val << " (" << nbits << " bits)" << std::endl;
   }
}

/* now all the image_configurations have been solved, tally them by size since we need them in order 
from smallest to largest. We're using multiprecision integers from the BOOST package now because the 
numbers are getting larger than 64-bits for n=7 */
std::map<unsigned, std::map<std::vector<unsigned>, multiprecision> > results_by_size;

/* tally_results callback. The result will be multiplied by its orbit size since we're only evaluating one
   image configuration for each orbit, then put in the results_by_size container */
struct tally_results {
   void operator() (const std::string &imgcfg, unsigned orbit_size, const std::vector<unsigned> &multiplicities) {
      /* find the size, which means the number of elements mapped by the one-to-many mappings being tallied */
      unsigned size = 0;
      for (unsigned j=0; j<multiplicities.size(); ++j) {
         size += multiplicities[j];
      }
      /* now how many items are in the orbit. Multiply since we only need to solve one member of the orbit
         and the same result applies to all members */
      std::map<std::string, boost::uint64_t>::const_iterator mi = solved_image_configurations.find(imgcfg);
      if (mi == solved_image_configurations.end() || mi->first != imgcfg) 
         throw std::runtime_error("can't find image configuration result for " + imgcfg);
      multiprecision mtmp = mi->second;
      mtmp *= orbit_size;
      results_by_size[size][multiplicities] += mtmp;
   }
};

void tally_results_by_size(void) {
   walk_image_configurations(tally_results());
}

/* the net value to inclusion exclusion from a fully-multiple mapping.
   If all of the possible unions of base mappings which form a specific fully-multiple mapping
   are enumerated, and the net value to inclusion exclusion is determined (i.e. minus pairwise, plus 
   3-wise, minus 4-wise, etc. etc.) then it's a very complicated situation, but it simplifies greatly 
   via binomial / multinomial formulas.It's simply the product of all structure sizes minus one,
   times -1 for each of the even structure sizes.
   */
int value_function(const std::vector<unsigned> & item) {
   int theoretical = 1;
   for (unsigned i=0; i<item.size(); ++i) {
      int x = item[i] -1;
      if (x&1) x=-x;
      theoretical *= x;
   }
   return theoretical;
}

/* dump out in case we need to see the intermediate results */
void dump_results_by_size(void) {
   for (std::map<unsigned, std::map<std::vector<unsigned>, multiprecision> >::const_iterator i = results_by_size.begin();
      i != results_by_size.end(); ++i) {
         std::cout << i->first << std::endl;
      for(std::map<std::vector<unsigned>, multiprecision>::const_iterator j = i->second.begin(); j != i->second.end(); ++j) {
         std::cout << "   ";
         for (unsigned k=0; k<j->first.size(); ++k) {
            std::cout << j->first[k] << " ";
         }
         std::cout << j->second << " ";
         multiprecision mpnet = j->second;
         mpnet *= value_function(j->first);
         std::cout << mpnet << std::endl;
      }
   }
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

int main(int argc, char *argv[]) {
   try {
      if (argc <2) throw std::runtime_error("usage: subsetperms nsetsize [v]erbose\n  where nsetsize is from 5 through 7");
      for (int i=1; i<argc; ++i) {
         if (argv[i][0] == 'v') bverbose = true;
         else if (argv[i][0] == 'c') bcomplementary = true;
         else {
            nsetsize = boost::lexical_cast<unsigned>(argv[i]);
         }
      }

      std::cout << "enumerating fully-multiple map types" << std::endl;
      enumerate_fully_multiple_map_types();
      std::cout << "found " << maptypes.size() << " maptypes" << std::endl;
      if (bverbose) {
         unsigned nitem = 0;
         for (std::set<std::vector<unsigned> >::const_iterator i = maptypes.begin(); i != maptypes.end(); ++i) {
            std::cout << ++nitem << ": ";
            for (unsigned j=0; j < i->size(); ++j) {
               std::cout << (*i)[j] << " ";
            }
            std::cout << std::endl;
         }
      }
      std::cout << "finding orbits for image multiplicity sets" << std::endl;
      make_pairsets();
      {
         time_t elapsed = time(NULL);
         find_image_orbits();
         elapsed = time(NULL) - elapsed;
         std::cout << elapsed << " seconds" << std::endl;
         validate_orbits();
      }
      if (bverbose) {
         for (unsigned i=0; i<orbits.size(); ++i) {
            std::cout << "Level " << i << std::endl;
            unsigned counter = 0;
            for (unsigned j=0; j< orbits[i].size(); ++j) {
               std::cout << " " << orbits[i][j];
               if (++counter == i + 1) {
                  counter = 0;
                  std::cout << std::endl;
               }
            }
         }
         std::vector<std::vector<std::string> > orbits;
      }

      std::cout << "enumerating sequences of sub-problems to solve" << std::endl;
      enumerate_image_configurations();
      std::cout << "found " << image_configurations.size() << " image_configurations" << std::endl;
      if (bverbose) {
         for (std::set<std::string>::const_iterator i = image_configurations.begin(); i != image_configurations.end(); ++i) {
            std::cout << "  " << *i << std::endl;
         }
      }

      std::cout << "precomputing domain bitmaps for image elements" << std::endl;
      make_domain_table();
      if (bverbose) {
         for (std::map<std::string, std::map<unsigned, std::vector<unsigned> > >::const_iterator i = precomputed.begin();
               i != precomputed.end(); ++i) {
            std::cout << i->first << std::endl;
            for (std::map<unsigned, std::vector<unsigned> >::const_iterator j = i->second.begin(); j != i->second.end(); ++j) {
               std::cout << "   " << j->first << ": ";
               for (unsigned k=0; k<j->second.size(); ++k) {
                  std::string s = std::bitset<32>(j->second[k]).to_string();
                  while(s.size() > nsetsize * (nsetsize-1) /2) s.erase(s.begin());
                  std::cout << s << " ";
               }
               std::cout << std::endl;
            }
         }
      }

      std::cout << "solving the image_configurations" << std::endl;
      solve_image_configurations();
      std::cout << "solved_image_configurations size: " << solved_image_configurations.size() << std::endl;

      std::cout << "tallying results by size" << std::endl;
      tally_results_by_size();
      if (bverbose) dump_results_by_size();

      std::cout << "computing final result" << std::endl;
      compute_final_result();

   } catch (std::exception &x) {
      std::cout << x.what() << std::endl;
      return 1;
   }
   return 0;
}
