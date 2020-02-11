
# This file was *autogenerated* from the file emm_gen.sage
from sage.all_cmdline import *   # import sage library

#!/usr/bin/env sage

import sys, time, datetime, argparse, logging
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler as ds
from operator import itemgetter

def parseArguments():
    parser = argparse.ArgumentParser()

    # positional mandatory arguments
    parser.add_argument('c', help='linear term for EC', type=int)
    parser.add_argument('d', help='constant term for EC', type=int)
    parser.add_argument('stop', help='ending degree for genetic search', type=int)

    # optional arguments
    parser.add_argument('-s', '-start', help='starting degree for genetic search',
     type=int, default=Integer(1), dest='start')
    parser.add_argument('-m', '-multiplier', help='Multiplies point by an integer using EC arithmetic.',
     type=int, default=Integer(1), dest='mult')
    parser.add_argument('-g', '-gauss', help='Determines whether to choose coefficients according to gaussian distribution',
     type=bool, default=False, dest='gauss')
    parser.add_argument('-n', '-polys', help='number of polys in population',
     type=int, default=Integer(200), dest='n')
    parser.add_argument('-b', '-best', help='number of best polys -- polys to keep',
     type=int, default=Integer(50), dest='best')
    parser.add_argument('-e', '-gens', help='total number of generations for genetic search',
     type=int, default=Integer(100), dest='gens')
    parser.add_argument('-v', '-var', help='Determines whether to vary mutation rate',
     type=bool, default=True, dest='var')
    parser.add_argument('-u', '-mu', help='starting mutation rate, be sure this is high when using var',
     type=float, default=RealNumber('1.0'), dest='mu')
    parser.add_argument('-k', '-skip', help='when to print intermediate results, also important for varying mutation rate',
     type=int, default=Integer(10), dest='skip')
    parser.add_argument('-t', '-threads', help='how many threads to use',
     type=int, default=Integer(10), dest='threads')

    args = parser.parse_args()
    return args

def elliptic_gen_alg(c,d, mult, degree, n, best, gens, mu=RealNumber('0.1'), skip=Integer(10),
                    f=None, gauss=False, var=False):
    param = [c,d,mult] #trick to let inner functions use arguments without making them globals
    def gen_point_from_poly(f): #We want the solution to f(x)=0 to be x-coord on elliptic curve y^2 = x^3 + cx + d
        if f.degree() == Integer(1):
            R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
            a, b = f.list() # b*x + a
            a = -a
            logger1.debug('a,b=%s,%s' % (a,b))
            if ZZ(b).is_square(): #is sqrt(b^3) an integer?
                B = sqrt(b**Integer(3)) #yes
                S = PolynomialRing(ZZ, names=('z',)); (z,) = S._first_ngens(1)
                if (z**Integer(2) - (a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3))).is_irreducible():
                    L = NumberField(x**Integer(2) - (a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3)), names=('y',)); (y,) = L._first_ngens(1)
                    E = EllipticCurve(L, [param[Integer(0)],param[Integer(1)]])
                    P = E(a/b, y/B)
                else:
                    y = sqrt(a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3))
                    E = EllipticCurve(QQ, [param[Integer(0)],param[Integer(1)]])
                    P = E(a/b, y/B)
                return P
            else:
                K = NumberField(x**Integer(2) - b**Integer(3), names=('B',)); (B,) = K._first_ngens(1)#No, explicitly create sqrt(b^3)
                S = PolynomialRing(K, names=('z',)); (z,) = S._first_ngens(1)
                if (z**Integer(2) - (a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3))).is_irreducible():
                    L = K.extension(z**Integer(2) - (a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3)), names=('y',)); (y,) = L._first_ngens(1)
                    M = L.absolute_field(names=('c',)); (c,) = M._first_ngens(1)
                    from_M, to_M = M.structure()
                else:
                    y = sqrt(a**Integer(3) + param[Integer(0)]*a*b**Integer(2) + param[Integer(1)]*b**Integer(3))
                    M = K.absolute_field(names=('w',)); (w,) = M._first_ngens(1)
                    from_M, to_M = M.structure()
                E = EllipticCurve(M,[param[Integer(0)],param[Integer(1)]])
                P = E(to_M(a/b), to_M(y)/to_M(B))
                return P
        else: # degree 2 or higher
            R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
            K = NumberField(f, names=('a',)); (a,) = K._first_ngens(1)
            S = PolynomialRing(K, names=('z',)); (z,) = S._first_ngens(1)
            if (z**Integer(2) - (a**Integer(3) + param[Integer(0)]*a + param[Integer(1)])).is_irreducible():
                L = K.extension(z**Integer(2) - (a**Integer(3) + param[Integer(0)]*a + param[Integer(1)]), names=('b',)); (b,) = L._first_ngens(1)
                M = L.absolute_field(names=('w',)); (w,) = M._first_ngens(1)
                from_M, to_M = M.structure()
            else:
                b = sqrt(a**Integer(3) + param[Integer(0)]*a + param[Integer(1)])
                M = K.absolute_field(names=('w',)); (w,) = M._first_ngens(1)
                from_M, to_M = M.structure()
            E = EllipticCurve(M,[param[Integer(0)],param[Integer(1)]])
            P = E(to_M(a), to_M(b))
            return P

    @parallel
    def elliptic_height(f):
        P = gen_point_from_poly(f)
        return [f,P.domain().base_ring().absolute_degree()*P.height()]

    def elliptic_height_is_nonzero(f):
        return elliptic_height(f)[Integer(1)] > Integer(2)**-Integer(50)

    def irred_and_not_torsion(f):
        if f.is_irreducible():
            if elliptic_height_is_nonzero(f):
                return True
        else:
            return False

    def poly_fix(f): #fixes problem in gen_point_from_poly by making leading coefficient of f positive
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        if f.leading_coefficient() < Integer(0):
            f = -Integer(1) * f
        return f

    def random_poly(deg):
        # set_random_seed()
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        f = poly_fix(R.random_element(deg, -Integer(10), Integer(10)+Integer(1), 'uniform'))
        while not f.is_irreducible() or f.degree() < deg:
            f = poly_fix(R.random_element(deg, -Integer(10), Integer(10)+Integer(1), 'uniform'))
        return f

    def random_poly_gauss(deg): #BUGGY
        # set_random_seed()
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        list = []
        for i in range(Integer(0),deg+Integer(1)):
            list = list + [ds(deg+Integer(5),algorithm="uniform+logtable")()]
        while list[deg] == Integer(0):
            list[deg] = ds(deg+Integer(5),algorithm="uniform+logtable")()
        f = poly_fix(R(list))
        while not f.is_irreducible():
            list = []
            for i in range(Integer(0),deg+Integer(1)):
                list = list + [ds(deg+Integer(5),algorithm="uniform+logtable")()]
            while list[deg] == Integer(0):
                list[deg] = ds(deg+Integer(5),algorithm="uniform+logtable")()
            f = poly_fix(R(list))
        return f

    def poly_pop(deg,n):
        return [random_poly(deg) for i in range(n)]

    def poly_pop_gauss(deg,n):
        return [random_poly_gauss(deg) for i in range(n)]

    def filterpoly(polylst): #filters polys in lst and returns list with [poly,height] entries
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        i = Integer(0) # how many loops before whole list has no polys with zero height

        polys_with_heights = [x[Integer(1)] for x in list(elliptic_height(polylst))]
        nonzero_heights = list(filter(lambda y: y[Integer(1)] > Integer(2)**-Integer(50), polys_with_heights))

        while(len(nonzero_heights) != len(polylst)): #need full list
            new_polylst = poly_pop(polylst[Integer(0)].degree(),len(polylst)-len(nonzero_heights))
            new_polylst_heights = [x[Integer(1)] for x in list(elliptic_height(new_polylst))]
            new_nonzero_heights = list(filter(lambda y: y[Integer(1)] > Integer(2)**-Integer(50), new_polylst_heights))
            nonzero_heights = nonzero_heights + new_nonzero_heights
            i += Integer(1)
        logger2.debug("filterpoly took %s loops to make full nonzero height list" % i)
        return nonzero_heights

    def crossover(poly1,poly2):
        flag = Integer(1) # 0 is "cross successful"
        count = Integer(0)
        lst1 = poly1.list()
        lst2 = poly2.list()
        templist = lst2
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        while (flag!=Integer(0) and count!=len(lst1)):
            for i in range(len(lst1)):
                if randint(Integer(0),Integer(1))==Integer(1):
                    templist[i]=lst1[i]
            temp_poly = R(templist)
            if irred_and_not_torsion(temp_poly):
                flag = Integer(0)
            else:
                count += Integer(1)
        if flag == Integer(1):
            return poly2
        else:
            return temp_poly

#Mutation code
    def swap(poly):
        flag = Integer(1)
        count = Integer(0)
        lst = poly.list()
        templist = lst
        R = PolynomialRing(ZZ, names=('x',)); (x,) = R._first_ngens(1)
        while (flag!=Integer(0) and count!=Integer(2)*binomial(len(lst),Integer(2))):
            # Bad choice code:
            # [i,j] = [choice(range(1,len(lst))) for i in range(2)] #swap indices
            # Remember, the LAST element of the polynomial list is the LEADING coeff of 1.
            # Never change that!
            i = randint(Integer(0),len(lst)-Integer(2)) # len(lst) - 1 is the last coeff, and randint is inclusive
            j = randint(Integer(0),len(lst)-Integer(2))
            templist[i] = lst[j]
            templist[j] = lst[i]
            temp_poly = R(templist)
            if irred_and_not_torsion(temp_poly):
                flag = Integer(0)
            else:
                count += Integer(1)
        if flag == Integer(1):
            return poly
        else:
            return temp_poly

    def mutate(poly,mu): # mu = 1 -> always mutate, mu = 0 -> never mutate
        if poly.degree == Integer(1):
            return poly
        else:
            mu_int = int(mu)
            mu_frac = mu - mu_int
            if random() < mu_frac:
                mu_int += Integer(1)
            return nest(swap,mu_int,poly)

    def new_child(parents,mu):
        poly1 = choice(parents)
        poly2 = choice(parents)
        tries = Integer(1)
        while poly2 == poly1 and tries <= Integer(20):
            poly2 = choice(parents)
            tries += Integer(1)
        if tries > Integer(10):
            logging.warning("poly1 == poly2 %s times in a row.", tries)
        child = crossover(poly1,poly2)
        child = mutate(child,mu)
        return elliptic_height(child)

#Beginning of genetic algorithm
    logging.info('starting deg %s genetic algorithm', degree)
    gen = Integer(0)
    logging.info('starting polypop computation')
    if gauss:
        polypop = poly_pop_gauss(degree,n)
    else:
        polypop = poly_pop(degree,n)

    # This is computed in parallel
    polys_with_heights = filterpoly(polypop) #create list of [poly,height] with nonzero height
    logging.debug('polys_with_heights = %s', polys_with_heights)

    polypop = [p[Integer(0)] for p in polys_with_heights]
    logging.info('finished polypop computation')
    logging.info('polypop = %s', polypop)

    while gen <= gens:
        logging.info('************************** Starting generation %s **************************', gen)

        population = [list(item) for item in set(tuple(lst) for lst in polys_with_heights)]
        population.sort(key = itemgetter(Integer(1)))
        logging.debug('Computed population of length %s', len(population))
#Printing
        if gen % skip == Integer(0):
            if var: #vary the mutation rate: goes down, but goes up if too few unique polys
                if gen != Integer(0):
                    p_n = float(n - len(population))/n
                    logging.debug('n = %s, len = %s, p_n=%s' % (n,len(population),p_n))
                    mu = mu - float(skip / gens) + p_n**Integer(2)
            logging.info('\nGeneration %s: best polynomial of degree %s is %s'
            ' with Mahler measure: %s.\nMutation rate: %s\n' % (gen,degree,population[Integer(0)][Integer(0)],population[Integer(0)][Integer(1)],mu))
        if gen == gens:
            if f is not None:
                for p in population[:best]:
                    print >> f, p[Integer(1)], "\t", p[Integer(0)], "\t", degree
                    #print('%s\t%s\t%s' % (p[1], p[0], degree), file=f)

#Mutation and Crosslink
        k = min(len(population), best)
        polys_with_heights = population[:k] #list of best polys in the population
        polypop = [p[Integer(0)] for p in polys_with_heights]
        logging.debug('polypop = %s', polypop)
        # This is computed in parallel
        new_children = [ new_child(polypop, mu) for i in range(n-k) ] # fill in the remaining slots with the crossbred polys
        logging.debug('new_children = %s',new_children)
        logging.debug('new_children has %s members', len(new_children))

        polys_with_heights = polys_with_heights + new_children
        logging.debug('polys_with_heights = %s', polys_with_heights)

        gen += Integer(1)
    return population[Integer(0)]

set_random_seed()
date = datetime.datetime.now()

if __name__ == '__main__':
    args = parseArguments()

    Parallelism().set(nproc=args.threads)
    
    logging.basicConfig(filename='ec-%s-%s-D%s-%s-%sT%s-%s.log' % 
                        (args.c,args.d,date.year,date.month,date.day,date.hour,date.minute),
                        format='%(asctime)s - %(name)-12s - %(levelname)s - %(message)s',
                        level=logging.DEBUG)

    # define a Handler which writes INFO messages or higher to the sys.stderr
    console = logging.StreamHandler()
    console.setLevel(logging.INFO)

    # set a format which is simpler for console use
    formatter = logging.Formatter('%(name)-12s: %(levelname)-8s %(message)s')
    # tell the handler to use this format
    console.setFormatter(formatter)
    # add the handler to the root logger
    logging.getLogger('').addHandler(console)

    # Now, define a couple of other loggers which might represent areas in your
    # application:

    logger1 = logging.getLogger('gen_point_from_poly')
    logger2 = logging.getLogger('filterpoly')

    with open("ec-%s-%s-output-D%s-%s-%sT%s-%s.txt" % 
        (args.c,args.d,date.year,date.month,date.day,date.hour,date.minute), 'w') as f:
        print >> f,"Height\tPoly\tDeg"
        #print("Height\tPoly\tDeg", file=f)
        for degree in range(args.start, args.stop+Integer(1)):
            #elliptic_gen_alg(c,d, mult, degree, n, best, gens, mu=0.1, skip, 
                             #f, gauss)
            elliptic_gen_alg(args.c,args.d,args.mult,degree, args.n, args.best, args.gens, args.mu, args.skip,
                             f, args.gauss, args.var)

    logging.info('Finished')

