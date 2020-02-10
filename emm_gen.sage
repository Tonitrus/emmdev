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
     type=int, default=1, dest='start')
    parser.add_argument('-m', '-multiplier', help='Multiplies point by an integer using EC arithmetic.',
     type=int, default=1, dest='mult')
    parser.add_argument('-g', '-gauss', help='Determines whether to choose coefficients according to gaussian distribution',
     type=bool, default=False, dest='gauss')
    parser.add_argument('-n', '-polys', help='number of polys in population',
     type=int, default=200, dest='n')
    parser.add_argument('-b', '-best', help='number of best polys -- polys to keep',
     type=int, default=50, dest='best')
    parser.add_argument('-e', '-gens', help='total number of generations for genetic search',
     type=int, default=100, dest='gens')
    parser.add_argument('-v', '-var', help='Determines whether to vary mutation rate',
     type=bool, default=True, dest='var')
    parser.add_argument('-u', '-mu', help='starting mutation rate, be sure this is high when using var',
     type=float, default=1.0, dest='mu')
    parser.add_argument('-k', '-skip', help='when to print intermediate results, also important for varying mutation rate',
     type=int, default=10, dest='skip')
    parser.add_argument('-t', '-threads', help='how many threads to use',
     type=int, default=10, dest='threads')

    args = parser.parse_args()
    return args

def flush():
    sys.stdout.flush()
    time.sleep(0.5)

def elliptic_gen_alg(c,d, mult, degree, n, best, gens, mu=0.1, skip=10,
                    f=None, gauss=False, var=False):
    param = [c,d,mult] #trick to let inner functions use arguments without making them globals
    def gen_point_from_poly(f): #We want the solution to f(x)=0 to be x-coord on elliptic curve y^2 = x^3 + cx + d
        if f.degree() == 1:
            R.<x> = PolynomialRing(ZZ)
            a, b = f.list() # b*x + a
            a = -a
            logger1.debug('a,b=%s,%s' % (a,b))
            if ZZ(b).is_square(): #is sqrt(b^3) an integer?
                B = sqrt(b^3) #yes
                S.<z> = PolynomialRing(ZZ)
                if (z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3)).is_irreducible():
                    L.<y> = NumberField(x^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3))
                    E = EllipticCurve(L, [param[0],param[1]])
                    P = E(a/b, y/B)
                else:
                    y = sqrt(a^3 + param[0]*a*b^2 + param[1]*b^3)
                    E = EllipticCurve(QQ, [param[0],param[1]])
                    P = E(a/b, y/B)
                return P
            else:
                K.<B> = NumberField(x^2 - b^3) #No, explicitly create sqrt(b^3)
                S.<z> = PolynomialRing(K)
                if (z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3)).is_irreducible():
                    L.<y> = K.extension(z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3))
                    M.<c> = L.absolute_field()
                    from_M, to_M = M.structure()
                else:
                    y = sqrt(a^3 + param[0]*a*b^2 + param[1]*b^3)
                    M.<w> = K.absolute_field()
                    from_M, to_M = M.structure()
                E = EllipticCurve(M,[param[0],param[1]])
                P = E(to_M(a/b), to_M(y)/to_M(B))
                return P
        else: # degree 2 or higher
            R.<x> = PolynomialRing(ZZ)
            K.<a> = NumberField(f)
            S.<z> = PolynomialRing(K)
            if (z^2 - (a^3 + param[0]*a + param[1])).is_irreducible():
                L.<b> = K.extension(z^2 - (a^3 + param[0]*a + param[1]))
                M.<w> = L.absolute_field()
                from_M, to_M = M.structure()
            else:
                b = sqrt(a^3 + param[0]*a + param[1])
                M.<w> = K.absolute_field()
                from_M, to_M = M.structure()
            E = EllipticCurve(M,[param[0],param[1]])
            P = E(to_M(a), to_M(b))
            return P

    @parallel
    def elliptic_height(f):
        P = gen_point_from_poly(f)
        return [f,P.domain().base_ring().absolute_degree()*P.height()]

    def elliptic_height_is_nonzero(f):
        return elliptic_height(f)[1] > 2^-50

    def irred_and_not_torsion(f):
        if f.is_irreducible():
            if elliptic_height_is_nonzero(f):
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
        while not f.is_irreducible() or f.degree() < deg:
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
        while not f.is_irreducible():
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
    def poly_with_elliptic_height(f):
        if f.degree() == 1:
            R.<x> = PolynomialRing(ZZ)
            a, b = f.list()
            a = -a
            logger2.debug('a,b=%s,%s' % (a,b))
            if ZZ(b).is_square(): #is sqrt(b^3) an integer?
                B = sqrt(b^3)
                S.<z> = PolynomialRing(ZZ)
                if (z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3)).is_irreducible():
                    L.<y> = NumberField(x^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3))
                    E = EllipticCurve(L, [param[0],param[1]])
                    P = param[2] * E(a/b, y/B)
                    return [f, 2 * P.height()]
                else:
                    y = sqrt(a^3 + param[0]*a*b^2 + param[1]*b^3)
                    E = EllipticCurve(QQ, [param[0],param[1]])
                    P = param[2] * E(a/b, y/B)
                    return [f, P.height()]
            else:
                K.<B> = NumberField(x^2 - b^3) #No, explicitly create sqrt(b^3)
                S.<z> = PolynomialRing(K)
                if (z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3)).is_irreducible():
                    L.<y> = K.extension(z^2 - (a^3 + param[0]*a*b^2 + param[1]*b^3))
                    M.<c> = L.absolute_field()
                    from_M, to_M = M.structure()
                else:
                    y = sqrt(a^3 + param[0]*a*b^2 + param[1]*b^3)
                    M.<w> = K.absolute_field()
                    from_M, to_M = M.structure()
                E = EllipticCurve(M,[param[0],param[1]])
                P = param[2] * E(to_M(a/b), to_M(y)/to_M(B))
                return [f, M.degree()*P.height()]
        else: # degree 2 or higher
            R.<x> = PolynomialRing(ZZ)
            K.<a> = NumberField(f)
            S.<z> = PolynomialRing(K)
            if (z^2 - (a^3 + param[0]*a + param[1])).is_irreducible():
                L.<b> = K.extension(z^2 - (a^3 + param[0]*a + param[1]))
                M.<w> = L.absolute_field()
                from_M, to_M = M.structure()
            else:
                b = sqrt(a^3 + param[0]*a + param[1])
                M.<w> = K.absolute_field()
                from_M, to_M = M.structure()
            E = EllipticCurve(M,[param[0],param[1]])
            P = param[2] * E(to_M(a), to_M(b))
            return [f, M.degree()*P.height()]

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
        if tries > 10:
            logger1.warning("poly1 == poly2 %s times in a row.", tries)
        child = crossover(poly1,poly2)
        child = mutate(child,mu)
        return child

#Beginning of genetic algorithm
    logging.info('starting deg %s genetic algorithm', degree)
    gen = 0
    logging.info('starting polypop computation')
    if gauss:
        polypop = poly_pop_gauss(degree,n)
    else:
        polypop = poly_pop(degree,n)
    logging.info('finished polypop computation')
    logging.info('polypop = %s', polypop)

    while gen <= gens:
        logging.info('************************** Starting generation %s **************************', gen)
        # This is computed in parallel
        population = Set([tuple(z[1]) for z in list(poly_with_elliptic_height(polypop))])
        population = list(population) #list has form [(poly,height)]
        population.sort(key = itemgetter(1))
        logging.debug('Computed population of length %s', len(population))
#Printing
        if gen % skip == 0:
            if var: #vary the mutation rate: goes down, but goes up if too few unique polys
                if gen != 0:
                    p_n = float(n - len(population))/n
                    logging.debug('p_n=%s', p_n)
                    mu = mu - float(skip / gens) + p_n^2
            logging.info('\nGeneration %s: best polynomial of degree %s is %s'
            ' with Mahler measure: %s.\nMutation rate: %s\n' % (gen,degree,population[0][0],population[0][1],mu))
        if gen == gens:
            if f is not None:
                for p in population[:best]:
                    print >> f, p[1], "\t", p[0], "\t", degree
                    #print('%s\t%s\t%s' % (p[1], p[0], degree), file=f)

#Mutation and Crosslink
            k = min(len(population), best)
            polypop = [p[0] for p in population[:k]] #list of best polys in the population
            new_children = [ new_child(polypop, mu) for i in range(n-k) ] # fill in the remaining slots with the crossbred polys
            polypop = polypop + new_children
            logging.debug('new_children has %s members', len(new_children))
        gen += 1
    return population[0]

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
    logger2 = logging.getLogger('poly_with_elliptic_height')

    with open("ec-%s-%s-output-D%s-%s-%sT%s-%s.txt" % 
        (args.c,args.d,date.year,date.month,date.day,date.hour,date.minute), 'w') as f:
        print >> f,"Height\tPoly\tDeg"
        #print("Height\tPoly\tDeg", file=f)
        for degree in range(args.start, args.stop+1):
            #elliptic_gen_alg(c,d, mult, degree, n, best, gens, mu=0.1, skip, 
                             #f, gauss)
            elliptic_gen_alg(args.c,args.d,args.mult,degree, args.n, args.best, args.gens, args.mu, args.skip,
                             f, args.gauss, args.var)

    logging.info('Finished')