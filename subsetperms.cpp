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

/* permuted maptypes. For example, the maptypes might have 3 2 2 as an entry since it is always
   descending. The permuted maptypes has all permutations of this, i.e.: 3 2 2, 2 3 2, 2 2 3
*/
std::set<std::vector<unsigned> > permuted_maptypes;

void permute_map_types(void) {
   for (std::set<std::vector<unsigned> >::const_iterator i=maptypes.begin(); i != maptypes.end(); ++i)
   {
      std::vector<unsigned> combos = *i;
      do {
         permuted_maptypes.insert(combos);
      } while(prev_permutation(combos.begin(), combos.end()));
   }
}


/* all possible subsets of 1..n of order two, using letters so A=1, B=2, etc. */
std::set<std::string> pairsets;

/* for each subset of order two, make a bitmap corresponding to subsets which are disjoint,
   eg. AB has a vector of bits corresponding to CD CE DE... */
std::map<std::string, std::vector<unsigned> > disjointmap;

/* orbits of image sets of subsets under permutation. First vector is for number of non-unique elements
  in image, can be 1 through n/2. Second vector is for strings, which are representatives of the orbits
  of image sets of specified size, and then a string representing the number of elements in the orbit. */
std::vector<std::vector<std::string> > orbits;

std::set<std::set<std::string> > prevorbits;

std::map<std::set<std::string>, unsigned> orbit_sizes;

unsigned imagesize = 0; /* to be incremented as we increase the size of image */

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
//      std::cout << s << std::endl;
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
   /* put an empty placeholder for index zero which is unused in this scheme */
   orbits.resize(1);

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

/* enumerate_image_configurations. In this routine there is a double-nested loop
   to combine each permuted maptype with the appropriate orbits to generate
   image configurations to solve. The orbits and permuted maptypes are combined by
   interlacing two letters (for the image element) with two digits (for the multiplicity) */
void enumerate_image_configurations(void) {

   for (std::set<std::vector<unsigned> >::const_iterator i=permuted_maptypes.begin();
      i != permuted_maptypes.end(); ++i)
   {
      const std::vector<unsigned> & item = *i;
      unsigned ncolumns = item.size();
      const std::string *snext = &orbits[ncolumns].front();

      unsigned norbits = orbits[ncolumns].size() / (ncolumns + 1);
      for (unsigned i=0; i<norbits; ++i) {
         std::string sitem;
         for (unsigned j=0; j<ncolumns; ++j) {
            sitem += *snext;
            std::string snumber = boost::lexical_cast<std::string>(item[j]);
            while (snumber.size() < 2) snumber.insert(snumber.begin(), '0');
            sitem +=snumber;
            ++snext;
         }
         image_configurations.insert(sitem);
         unsigned orbit_size = boost::lexical_cast<unsigned>(*snext);
         snext++;
      }
   }
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

void add_next_vector(std::map<unsigned, boost::uint64_t> &mx, 
                     const std::map<unsigned, boost::uint64_t> &m1,
                     const std::vector<unsigned> &v1)
{
   mx.clear();
   /* go through the existing level of bitmaps */
   for(std::map<unsigned, boost::uint64_t>::const_iterator i = m1.begin(); i != m1.end(); ++i) {
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
   std::map<unsigned, boost::uint64_t> m1;
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
      for(std::map<unsigned, boost::uint64_t>::const_iterator i = vs.back().m1.begin(); i != vs.back().m1.end(); ++i) {
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

void tally_results_by_size(void) {
   /* go through all of the maptypes */
   for (std::set<std::vector<unsigned> >::const_iterator i=maptypes.begin(); i != maptypes.end(); ++i)
   {
      /* find the size, which means the number of elements mapped by the one-to-many mappings being tallied */
      unsigned size = 0;
      for (unsigned j=0; j<i->size(); ++j) {
         size += (*i)[j];
      }

      /* now we have to go through all permutations of the maptype, and then through all of the 
         orbits and tally up all of the fully-multiple mappings that have the required multiplicity
         values */
      std::vector<unsigned> combos = *i; /* the original, ordered multiplicity counts */
      multiprecision total_all_combos = 0;
      do {
         multiprecision total_this_orbit = 0; /* initialize to zero, we will update it */
         unsigned nimageelements = combos.size();
         /* next we need to go through all the orbits for nimagelements */
         const std::string *snext = &orbits[nimageelements].front();
         /* It's a repeated set of nimagelement strings followed by a number string, 
            so divide to get the number of orbits */
         unsigned norbits = orbits[nimageelements].size() / (nimageelements + 1);
         /* now go through each orbit and combine the orbit and the count combination 
            to get the corresponding image_configuration that was solved */
         for (unsigned i=0; i<norbits; ++i) {
            std::string sitem;
            for (unsigned j=0; j<combos.size(); ++j) {
               sitem += *snext;
               std::string snumber = boost::lexical_cast<std::string>(combos[j]);
               while (snumber.size() < 2) snumber.insert(snumber.begin(), '0');
               sitem +=snumber;
               ++snext;
            }
            /* now how many items are in the orbit. Multiply since we only need to solve one member of the orbit
               and the same result applies to all members */
            unsigned orbit_size = boost::lexical_cast<unsigned>(*snext);
            std::map<std::string, boost::uint64_t>::const_iterator mi = solved_image_configurations.find(sitem);
            if (mi == solved_image_configurations.end() || mi->first != sitem) throw std::runtime_error("can't find structure " + sitem);
            multiprecision mtmp = mi->second;
            mtmp *= orbit_size;
            total_this_orbit += mtmp;

            snext++; /* go on to next orbit */
         }
         total_all_combos += total_this_orbit;
      } while(prev_permutation(combos.begin(), combos.end()));
      /* now we've added all combinations times all orbits, so this is the grand total of number of 
         mappings which have the required numbers of image multiplicities */
      results_by_size[size][*i] = total_all_combos;
   }
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

      std::cout << "enumerating non-invertible map types" << std::endl;
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

      std::cout << "permuting the non-invertible map types" << std::endl;
      permute_map_types();
      std::cout << "found " << permuted_maptypes.size() << " permuted maptypes" << std::endl;
      if (bverbose) {
         unsigned nitem = 0;
         for (std::set<std::vector<unsigned> >::const_iterator i = permuted_maptypes.begin(); i != permuted_maptypes.end(); ++i) {
            std::cout << ++nitem << ": ";
            for (unsigned j=0; j < i->size(); ++j) {
               std::cout << (*i)[j] << " ";
            }
            std::cout << std::endl;
         }
      }

      std::cout << "finding orbits for image multiplicity sets" << std::endl;
      {
         time_t elapsed = time(NULL);
         find_image_orbits();
         elapsed = time(NULL) - elapsed;
         std::cout << elapsed << " seconds" << std::endl;
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
