/*
 *  superstar.c -- David Richerby, 2011-12.
 *  Superstar simulator that keeps track of which vertices are in a
 *  different state than their out-neighbours so can cause a state
 *  change if selected for reproduction.
 *
 *  WARNING!  This code will not compile as-is.  For efficiency, the
 *  simulation parameters are set as compile-time constants.  It is
 *  recommended that the program be compiled with the runsuperstar
 *  script.  If you are not using that script, replace the values
 *  __RVAL, __QVAL, __KVAL, __LVAL, __MVAL and __TVAL with the
 *  appropriate numerical values and compile with as many
 *  optimizations enabled as possible.  (With gcc, use -O3 .)
 *  
 *
 *  $Id: superstar.c,v 1.13 2012/01/18 18:56:20 davidr Exp $
 */

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/*
 *  Simulation parameters.
 */
#define r __RVAL
#define q __QVAL
#define K __KVAL
#define L __LVAL
#define M __MVAL
#define TRIALS __TVAL


/*
 *  Useful constants.
 */
#define N  ((L)*((M)+((K)-2))+1)  /* Total number of vertices.        */
#define NONRES  ((L)*((K)-2)+1)   /* Number of non-reservoir vertices.*/
#define CENTRE  ((L)*((K)-2))     /* Index of centre vertex in vlist. */

#define FIRSTSTLEAF ((L)/2)   /* First leaf vertex of the reservoir   */
                              /*     fitness search tree.             */

/*
 *  Vertex states
 */
#define MUTANT     0
#define NONMUT     1
#define ACTIVE     0
#define DORMANT    2
#define ACT_MUT    0  /* Active mutant.                               */
#define ACT_NON    1  /* Active non-mutant.                           */
#define DOR_MUT    2  /* Dormant mutant.                              */
#define DOR_NON    3  /* Dormant non-mutant.                          */
#define NUMSTATES  4


/**********************************************************************/
/* Globals                                                            */
/**********************************************************************/

int state[NONRES];          /* State of each vertex.                  */
int numinstate[NUMSTATES];  /* Number of vertices in each state.      */
int vlist[2][NONRES];       /* List of vertices in each state.        */
int posn[NONRES];  /* Position of each vertex in the one list it's in.*/
int totresactfit;  /* Total fitness of active vertices in reservoirs. */
int totnonresactfit;        /* Total fitness of other active vertices.*/
int resmut[L];     /* Number of mutants in each reservoir.            */
int resmuts;       /* Total number of mutants in reservoirs.          */
int resstate[L];   /* Are mutants or non-mutants active in each res.? */
int resactfit[L];  /* Fitness of active vertices in each leaf.        */
int restree[L];    /* Search tree for reservoir fitness.              */


/**********************************************************************/
/* Random number generation                                           */
/**********************************************************************/

/*
 *  A re-implementation of the algorithm used by glibc 2.12.2 (and,
 *  presumably other versions), based on Peter Selinger's description
 *  at http://www.mscs.dal.ca/~selinger/random/
 *  Gives identical results to glibc's random() but included here for
 *  reproducability of results on other systems.
 */

#define POOLSIZE 34
unsigned int rndpool[POOLSIZE];
int rndidx = 0;

static unsigned int localrandom ()
{
	rndidx = (rndidx + 1) % POOLSIZE;
	rndpool[rndidx%POOLSIZE] = rndpool[(rndidx+31)%POOLSIZE]
		                         + rndpool[(rndidx+3)%POOLSIZE];
	return ((unsigned)rndpool[rndidx%POOLSIZE]) >> 1;
}

static void localsrandom (unsigned int seed)
{
	long long x;
	int i;

	rndpool[0] = seed;
	for (i = 1; i < 31; i++)
	{
		rndpool[i] = (16807LL * rndpool[i-1]) % 2147483647;
		if (rndpool[i] < 0)
			rndpool[i] += 2147483647;
	}
	rndpool[31] = rndpool[0];
	rndpool[32] = rndpool[1];
	rndpool[33] = rndpool[2];

	rndidx = -1;
	for (i = 34; i < 344; i++)
		(void)localrandom();
}

/**********************************************************************/
/* Vertex state manipulation                                          */
/**********************************************************************/

/*
 *  True if the chain/centre vertex with index v is a mutant (active or
 *  dormant).
*/
#define ISMUTANT(v) ((state[(v)] % 2) == 0)

/*
 *  void setvstate (int v, int s)
 *  Change the state of vertex v to s, adjusting total fitness of
 *  active vertices as appropriate.
 */
void setvstate (int v, int s)
{
    int olds = state[v];

	/*
	 *  Remove from old state.
	 */
	numinstate[olds]--;
	if (olds <= ACT_NON)
	{
		int movedvtx = vlist[olds][numinstate[olds]];

		vlist[olds][posn[v]] = movedvtx;
		posn[movedvtx] = posn[v];
		if (olds == ACT_NON)
			totnonresactfit -= q;
		else
			totnonresactfit -= r;
	}

	/*
	 *  Place in new state.
	 */
	state[v] = s;
	if (s <= ACT_NON)
	{
		vlist[s][numinstate[s]] = v;
		posn[v] = numinstate[s];
		if (s == ACT_NON)
			totnonresactfit += q;
		else
			totnonresactfit += r;
	}
	numinstate[s]++;
}

/*
 *  Macros for manipulating reservoir fitness search tree.
 */
#define LCHILD(x) (2*(x)+1)       /* Left child of node x.           */
#define RCHILD(x) (2*(x)+2)       /* Right child of node x.          */
#define PARENT(x) (((x)-1)/2)     /* Parent of node x.               */
#define ISLCHILD(x) ((x)%2 == 1)  /* True iff node x is a left child.*/

/*
 *  void incresfit (int leaf, int delta)
 *  Increase the fitness of the leaf-th reservoir by delta and update
 *  the reservoir fitness search tree accordingly.
 */
void incresfit (int leaf, int delta)
{
	int i;

	for (i=leaf; i>0; i = PARENT(i))
		if (ISLCHILD(i))
			restree[PARENT(i)] += delta;

	resactfit[leaf] += delta;
	totresactfit += delta;
}

/*
 *  void flipresstate (int leaf)
 *  Flip the state of the leaf-th reservoir from mutants being active
 *  to non-mutants, or vice versa, making the necessary changes to the
 *  leaf's fitness and the search tree.
 */
void flipresstate (int leaf)
{
	int delta;

	delta = M * q - (r + q) * resmut[leaf];
	if (resstate[leaf] == ACT_NON)
		delta *= -1;

	resstate[leaf] = 1 - resstate[leaf];

	incresfit (leaf, delta);
}


/**********************************************************************/
/* Main program                                                       */
/**********************************************************************/

/*
 *  A vertex is "active" if it sends an edge to a vertex in the
 *  opposite state; otherwise, it is "dormant".
 */

int main(int argc, char **argv)
{
	int i;            /* General loop counter.                        */
	int t;            /* Loop counter for trials.                     */
	int rnd;          /* Output of random().                          */

	int src, dest;    /* Source and target vertices of reproduction.  */
    int newstate;     /* The new state for the target vertex.         */

    int extinctions,  /* The number of extinctions and fixations in a */
        fixations;    /*     batch of simulations.                    */

	unsigned int seed;  /* Random number generator seed value.        */

	/*
	 *  Print simulation parameters.
	 */
    setbuf (stdout, NULL); /* Turn off buffering on stdout so         */
						   /*     progress reports appear properly.   */
	printf ("$Id: superstar.c,v 1.13 2012/01/18 18:56:20 davidr Exp $\n");
	printf ("K=%d, L=%d, M=%d, N=%d, r=%d/%d, %d trials\n", K, L, M, N, r, q, TRIALS);

    /*
	 *  Initialize random number generator.  If there is one, use the
	 *  first command-line parameter as the seed; otherwise, use the
	 *  system time.
	 */
	seed = time (NULL);
	if (argc > 1)
	{
		char *p;

		long int val=strtol (argv[1], &p, 10);
		if (p == argv[1] || *p != '\0' || val < 0)
		{
			fprintf (stderr, "Error.  If an argument is supplied, it must be a positive integer seed the\nrandom number generator.  Call with no argument to seed with the system time.\n");
			return 1;
		}
		seed = (unsigned)val;
	}

	printf ("Random seed = %u\n\n", seed);
	
	localsrandom (seed);

	/*
	 *  Initialize statistics collection.
	 */
	extinctions = fixations = 0;

    /*
	 *  Outer simulation loop (simulate TRIALS times to fixation).
	 */
	for (t = 1; t <= TRIALS; t++)
	{
		/*
		 *  Initialize mutant lists.  The initial state is fully
		 *  consistent: everything is a dormant non-mutant, except the
		 *  centre, which is an active non-mutant.  In a moment, we'll
		 *  pick an initial mutant and change its state.
		 */
		numinstate[ACT_MUT] = 0;
		numinstate[ACT_NON] = 1;
		numinstate[DOR_MUT] = 0;
		numinstate[DOR_NON] = NONRES-1;

		for (i = 0; i < CENTRE; i++)
			state[i] = DOR_NON;

		vlist[ACT_NON][0] = CENTRE;
		posn[CENTRE] = 0;
		state[CENTRE] = ACT_NON;

		memset (resmut, 0, L * sizeof (int));
		memset (resactfit, 0, L * sizeof (int));
		memset (resstate, 0, L * sizeof (int));
		memset (restree, 0, L * sizeof (int));

		resmuts = 0;
		totresactfit = 0;
		totnonresactfit = q;

		/*
		 *  Choose initial mutant.
		 */
		rnd = localrandom() % N;

		/*
		 *  Initial mutant is a reservoir vertex.  WLOG, we may place
		 *  it in the first leaf.  And the active vertices are already
		 *  correct: the centre is active and any leaf whose first
		 *  chain vertex is a non-mutant has the mutants active, even
		 *  if there aren't actually any.
		 */
		if (rnd > CENTRE)
		{
			resmut[0] = 1;
			resmuts = 1;
			incresfit (0, r);
		}
		/*
		 *  Initial mutant is in a chain.  If it's the first vertex in
		 *  its chain, the non-mutants in the leaf's reservoir are
		 *  active; otherwise, the mutant's predecessor in the chain
		 *  is.
		 */
		else if (rnd < CENTRE) 
		{
			setvstate (rnd, ACT_MUT);

			if (rnd < L) /* Head of the chain.  */
				flipresstate (rnd);
			else
				setvstate (rnd-L, ACT_NON);
		}
		/*
		 *  Initial mutant is in the centre.  The tail of each chain
		 *  becomes active.
		 */
		else
		{
			setvstate (rnd, ACT_MUT);
			for (i = L*(K-3); i < CENTRE; i++)
				setvstate (i, ACT_NON);
		}

		/*
		 *  Inner simulation loop (simulate until the mutants take
		 *  over or die out).
		 */
		while (numinstate[ACT_MUT] + numinstate[DOR_MUT] + resmuts > 0
			   && numinstate[ACT_MUT] + numinstate[DOR_MUT] + resmuts < N)
		{
			/*
			 *  Choose a source from the set of active vertices.
			 */
			rnd = localrandom() % (totnonresactfit + totresactfit);

			/*
			 *  Source is a reservoir vertex.
			 */
			if (rnd < totresactfit)
			{
				int leaf = 0;

				/*
				 *  Find which leaf's reservoir we've hit.
				 */
				while (leaf < FIRSTSTLEAF)
				{
					if (rnd < restree[leaf])
						leaf = LCHILD(leaf);
					else
					{
						rnd -= restree[leaf];
						if (rnd < resactfit[leaf])
							break;
						rnd -= resactfit[leaf];
						leaf = RCHILD(leaf);
					}
				}

				/* Don't need to set dest, as the the index of the
				 * first vertex of the leaf-th leaf is just leaf. */
				newstate = resstate[leaf];

				if (K == 3)
				{
					if (resstate[leaf] == state[CENTRE]%2)
						newstate += DORMANT;
				}
				else
				{
					if (resstate[leaf] == state[leaf+L]%2)
						newstate += DORMANT;
				}
				setvstate(leaf, newstate);

				/*
				 *  The head of the chain has flipped state so all
				 *  active vertices in the leaf's reservoir become
				 *  dormant and vice-versa.
				 */
				flipresstate(leaf);
			}
			else
			{
				rnd -= totresactfit;

				if (rnd < r * numinstate[ACT_MUT])
					src = vlist[ACT_MUT][rnd/r];
				else
					src = vlist[ACT_NON][(rnd - r * numinstate[ACT_MUT])/q];

				/*
				 *  If the source is a chain vertex...
				 */
				if (src < CENTRE)
				{
					int chainpos = src / L;

					/*
					 *  Last vertex in its chain.
					 */
					if (chainpos == K-3)
					{
						setvstate (CENTRE, state[src]);

						/*
						 *  Centre is changing state so need to flip
						 *  active/dormant for chain tails.
						 */
						for (i = L*(K-3); i < CENTRE; i++)
							setvstate (i, (state[i] + DORMANT) % NUMSTATES);
					}
					else
					/*
					 *  Not the last vertex in its chain.
					 */
					{
						dest = src+L;
						newstate = state[src];

						if (K > 3 && chainpos == K-4)
						{
							if ((ISMUTANT(src)) == (ISMUTANT(CENTRE)))
								newstate += DORMANT;
						}
						else if (K > 4)
						{
							if ((ISMUTANT(src)) == (ISMUTANT(dest+L)))
								newstate += DORMANT;
						}
						setvstate (src, state[src] + DORMANT);
						setvstate (dest, newstate);			
					}
				}
				/*
				 *  If the source is the centre...  Since the centre is
				 *  the only vertex with more than one out-edge, this is
				 *  the only case where an active vertex might not update
				 *  anything.
				 */
				else
				{
					int delta = 0;
					int dest = 0;
					int leaf = localrandom() % L;

					dest = localrandom() % M;

					if ((ISMUTANT(CENTRE)) && dest >= resmut[leaf])
					{
						resmut[leaf]++;
						resmuts++;
						if (resstate[leaf] == ACT_MUT)
							delta = r;
						else
							delta = -q;
					}
					else if (!ISMUTANT(CENTRE) && dest < resmut[leaf])
					{
						resmut[leaf]--;
						resmuts--;
						if (resstate[leaf] == ACT_MUT)
							delta = -r;
						else
							delta = q;
					}
					if (delta != 0)
						incresfit (leaf, delta);
				}
			}
		} /* End of inner simulation loop. */

		/*
		 *  Statistics collection.
		 */
		if (numinstate[ACT_MUT] + numinstate[DOR_MUT] + resmuts == 0)
			extinctions++;
		else
			fixations++;

		/*
		 *  Report progress every 10 trials and at the end.
		 */
		if (t % 10 == 0 || t == TRIALS) {
			if (isatty (1)) {
				printf ("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
                        "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
						"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b");
			}
			printf ("t=%-10d  Nfix=%-10d  Next=%-10d  Pfix=%-1.4f ",
					t, fixations, extinctions, fixations/(double)t);
					
			if (!isatty (1)) {
				printf ("\n");
			}
		}
	}

	printf ("\n");

	return 0;
}
