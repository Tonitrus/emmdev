#!/usr/bin/env sage

import sys, time, datetime, argparse
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler as ds
from operator import itemgetter
import logging

# if len(sys.argv) != 7:
#   print("Usage: %s <c> <d> <multiplier> <start> <stop> <gauss>" % sys.argv[0])
#   print("Outputs a file containing the smallest height polynomials on the elliptic curve y^2 = x^3 + cx + d, starting with degree start and ending with degree stop.")
#   sys.exit(1)

def parseArguments():
    parser = argparse.ArgumentParser()

    # positional mandatory arguments
    parser.add_argument('c', help='linear term for EC', type=int)
    parser.add_argument('d', help='constant term for EC', type=int)
    parser.add_argument('stop', help='ending degree for genetic search', type=int)

    # optional arguments
    parser.add_argument('-s', '-start', help='starting degree for genetic search', type=int, default=1, dest='start')
    parser.add_argument('-m', '-multiplier', help='Multiplies point by an integer using EC arithmetic.', type=int, default=1, dest='mult')
    parser.add_argument('-g', '-gauss', help='Determines whether to choose coefficients according to gaussian distribution', type=bool, default=False, dest='gauss')
    parser.add_argument('-n', '-polys', help='number of polys in population', type=int, default=200, dest='n')
    parser.add_argument('-b', '-best', help='number of best polys -- polys to keep', type=int, default=50, dest='best')
    parser.add_argument('-e', '-gens', help='total number of generations for genetic search', type=int, default=100, dest='gens')
    parser.add_argument('-v', '-var', help='Determines whether to vary mutation rate', type=bool, default=False, dest='var')
    parser.add_argument('-u', '-mu', help='starting mutation rate, be sure this is high when using var', type=float, default=1.0, dest='mu')
    parser.add_argument('-k', '-skip', help='when to print intermediate results, also important for varying mutation rate', type=int, default=10, dest='skip')
    parser.add_argument('-t', '-threads', help='how many threads to use', type=int, default=10, dest='threads')

    args = parser.parse_args()
    return args

def flush():
    sys.stdout.flush()
    time.sleep(0.5)

def elliptic_gen_alg(c,d, mult, degree, n, best, gens, mu=0.1, skip=10, f=None, warnings=False, debug=True, print_best=True, gauss=False, var=False):
    param = [c,d] #trick to let inner functions use arguments without making them globals
    def lattes(f, debug=False): #We want the solution to f(x)=0 to be x-coord on elliptic curve y^2 = x^3 + cx + d
        if f.degree() == 1:
            R.<x> = PolynomialRing(ZZ)
            a, b = f.list()
            a = -a
            if debug: print "a,b=", a,b
            PS.<x,y> = ProjectiveSpace(QQ,1)
            lattes = DynamicalSystem_projective([x^4-2*param[0]*x^2*y^2-8*param[1]*x*y^3+param[0]^2*y^4,4*x^3*y+4*param[0]*x*y^3+4*param[1]*y^4])
            P = PS(a/b)
            S.<z> = PolynomialRing(ZZ)
            if (z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3)).is_irreducible():
                return 2 * lattes.canonical_height(P)
            else:
                return lattes.canonical_height(P)
        else: # degree 2 or higher
            R.<x> = PolynomialRing(ZZ)
            K.<a> = NumberField(f)
            PSK.<x,y> = ProjectiveSpace(K,1)
            lattes = DynamicalSystem_projective([x^4-2*param[0]*x^2*y^2-8*param[1]*x*y^3+param[0]^2*y^4,4*x^3*y+4*param[0]*x*y^3+4*param[1]*y^4])
            P = PSK(a)
            S.<z> = PolynomialRing(K)
            if (z^2 - (a^3 + param[0]*a + param[1])).is_irreducible():
                return 2 * f.degree() * lattes.canonical_height(P)
            else:
                return f.degree() * lattes.canonical_height(P)

    def irred_and_not_torsion(f):
        if f.is_irreducible():
            if f.degree() == 1:
                R.<x> = PolynomialRing(ZZ)
                a, b = f.list()
                a = -a
                PS.<x,y> = ProjectiveSpace(QQ,1)
                lattes = DynamicalSystem_projective([x^4-2*param[0]*x^2*y^2-8*param[1]*x*y^3+param[0]^2*y^4,4*x^3*y+4*param[0]*x*y^3+4*param[1]*y^4])
                P = PS(a/b)
                if not P.is_preperiodic(lattes):
                    return True
            else:
                R.<x> = PolynomialRing(ZZ)
                K.<a> = NumberField(f)
                PSK.<x,y> = ProjectiveSpace(K,1)
                lattes = DynamicalSystem_projective([x^4-2*param[0]*x^2*y^2-8*param[1]*x*y^3+param[0]^2*y^4,4*x^3*y+4*param[0]*x*y^3+4*param[1]*y^4])
                P = PSK(a)
                if not P.is_preperiodic(lattes):
                    return True
        else:
            return False

    def poly_fix(f): #fixes problem in gen_point_from_poly by making leading coefficient of f positive
        R.<x> = PolynomialRing(ZZ)
        if f.leading_coefficient() < 0:
            f = -1 * f
        return f

    def random_poly(deg):
        # set_random_seed()
        R.<x> = PolynomialRing(ZZ)
        f = poly_fix(R.random_element(deg, -10, 10+1, 'uniform'))
        while not irred_and_not_torsion(f) or f.degree() < deg:
            f = poly_fix(R.random_element(deg, -10, 10+1, 'uniform'))
        return f

    def random_poly_gauss(deg): #BUGGY
        # set_random_seed()
        R.<x> = PolynomialRing(ZZ)
        list = []
        for i in range(0,deg+1):
            list = list + [ds(deg+5,algorithm="uniform+logtable")()]
        while list[deg] == 0:
            list[deg] = ds(deg+5,algorithm="uniform+logtable")()
        f = poly_fix(R(list))
        while not irred_and_not_torsion(f):
            list = []
            for i in range(0,deg+1):
                list = list + [ds(deg+5,algorithm="uniform+logtable")()]
            while list[deg] == 0:
                list[deg] = ds(deg+5,algorithm="uniform+logtable")()
            f = poly_fix(R(list))
        return f

    def poly_pop(deg,n):
        #return [z[1] for z in list(random_poly([deg for i in range(n)]))]
        return [random_poly(deg) for i in range(n)]

    def poly_pop_gauss(deg,n):
        #return [z[1] for z in list(random_poly([deg for i in range(n)]))]
        return [random_poly_gauss(deg) for i in range(n)]

    @parallel
    def poly_with_elliptic_height(f, debug=False):
        return [f, lattes(f)]

    def crossover(poly1,poly2):
        flag = 1 # 0 is "cross successful"
        count = 0
        lst1 = poly1.list()
        lst2 = poly2.list()
        templist = lst2
        R.<x> = PolynomialRing(ZZ)
        while (flag!=0 and count!=len(lst1)):
            for i in range(len(lst1)):
                if randint(0,1)==1:
                    templist[i]=lst1[i]
            temp_poly = R(templist)
            if irred_and_not_torsion(temp_poly):
                flag = 0
            else:
                count += 1
        if flag == 1:
            return poly2
        else:
            return temp_poly

#Mutation code
    def swap(poly):
        flag = 1
        count = 0
        lst = poly.list()
        templist = lst
        R.<x> = PolynomialRing(ZZ)
        while (flag!=0 and count!=2*binomial(len(lst),2)):
            # Bad choice code:
            # [i,j] = [choice(range(1,len(lst))) for i in range(2)] #swap indices
            # Remember, the LAST element of the polynomial list is the LEADING coeff of 1.
            # Never change that!
            i = randint(0,len(lst)-2) # len(lst) - 1 is the last coeff, and randint is inclusive
            j = randint(0,len(lst)-2)
            templist[i] = lst[j]
            templist[j] = lst[i]
            temp_poly = R(templist)
            if irred_and_not_torsion(temp_poly):
                flag = 0
            else:
                count += 1
        if flag == 1:
            return poly
        else:
            return temp_poly

    def mutate(poly,mu): # mu = 1 -> always mutate, mu = 0 -> never mutate
        if poly.degree == 1:
            return poly
        else:
            mu_int = int(mu)
            mu_frac = mu - mu_int
            if random() < mu_frac:
                mu_int += 1
            return nest(swap,mu_int,poly)

    def new_child(parents,mu, warnings=False):
        poly1 = choice(parents)
        poly2 = choice(parents)
        tries = 1
        while poly2 == poly1 and tries <= 20:
            poly2 = choice(parents)
            tries += 1
        if warnings and tries > 10: print "Warning: poly1 == poly2", tries, "times in a row."
        child = crossover(poly1,poly2)
        child = mutate(child,mu)
        return child

#Beginning of genetic algorithm
    gen = 0
    if debug:
        print "starting polypop computation"
        flush()
    if gauss:
        polypop = poly_pop_gauss(degree,n)
    else:
        polypop = poly_pop(degree,n)
    if debug:
        print "finished polypop computation"
        print "polypop =", polypop
        flush()
    while gen <= gens:
        if debug:
            print "************************** Starting generation", gen, "**************************"
            flush()
        # This is computed in parallel
        population = Set([tuple(z[1]) for z in list(poly_with_elliptic_height(polypop))])
        population = list(population)
        population.sort(key = itemgetter(1))
        if debug:
            print "Computed population of length", len(population)
            #print "population (with heights) =", population
            flush()
#Printing
        if gen % skip == 0:
            if var: #vary the mutation rate: goes down, but goes up if too few unique polys
                if gen != 0:
                    p_n = float((n - len(population))/(n))
                    mu = mu - float(skip / gens) + p_n^2
            print(('\nGeneration {0}: best polynomial of degree {1} is {2}'
            ' with Mahler measure: {3}.\nMutation rate: {4}\n').format(gen,degree,population[0][0],population[0][1],mu))
            flush()
        if gen == gens:
            if f is not None:
                for p in population[:best]:
                    print >> f, p[1], "\t", p[0], "\t", degree

#Mutation and Crosslink
        k = min(len(population), best)
        polypop = [p[0] for p in population[:k]]
        # new_child = [z[1] for z in list(new_children( [(polypop,mu) for i in range(n-best)] ))]
        new_children = [ new_child(polypop,mu, warnings) for i in range(n-k) ]
        polypop = polypop + new_children
        if debug:
            print "New population polypop =", polypop
            print "has", len(polypop), "members."
            flush()
        gen += 1
    return population[0]

set_random_seed()
date = datetime.datetime.now()

if __name__ == '__main__':
    args = parseArguments()

    Parallelism().set(nproc=args.threads)
    
    logging.basicConfig(filename='lec-%s-%s-D%s-%s-%sT%s-%s.log' % (args.c,args.d,date.year,date.month,date.day,date.hour,date.minute), format='%(asctime)s - %(levelname)s - %(message)s', level=logging.INFO)

    with open("lec-%s-%s-output-D%s-%s-%sT%s-%s.txt" % (args.c,args.d,date.year,date.month,date.day,date.hour,date.minute), 'w') as f:
        print >> f,"Height\tPoly\tDeg"
        for degree in range(args.start, args.stop+1):
            elliptic_gen_alg(args.c,args.d,args.mult,degree, args.n, args.best, args.gens, args.mu, args.skip, f, True, True, True, args.gauss, args.var)

    print "Finished"