def genFBase(N, fSize):
  fBase = []
  i = 1
  while len(fBase) < fSize:
    fBase = [-1] + filter(lambda p: kronecker(N, p) == 1, primes_first_n(fSize * 3 * i))
    i += 1

  fBase = fBase[0:fSize]
  return fBase

def g(p, k, N):
  if p == 2:
    return 2 * (N % 8 == 1)
  elif p % k == 0:
    return 1 / p
  else:
    return 2 / p

def knuthSchroeppel(k, N, fBase):
  return floor(numerical_approx(sum(map(lambda p: g(p, k, N) * log(p) - 1 / 2 * log(k), fBase[1:]))))

def testFunc(kn, M, pmax, T):
  return floor(log(M * sqrt(kn / 2) / (pmax ** T)))

def divFac(p, fBase):
  temp = p
  vecOfPws = [0 for i in fBase]
  if p < 0:
    vecOfPws[0] = 1
  num = 1
  for f in fBase[1:]:
    i = 0
    while temp % f == 0 and temp != 0:
      temp = temp / f
      i += 1
    vecOfPws[num] = i
    temp = p
    num += 1
  smooth = product(map(lambda x, y: x ** y, fBase, vecOfPws))
  return (p / smooth, vecOfPws)

def mpqs(N):
  numOfDigits = int(gp("length(Str({}))".format(N)))
  T = 0.0268849 * numOfDigits + 0.783929
  M = ceil((386 * (numOfDigits**2)) - (23209.3 * numOfDigits) + 352768)
  fSize = ceil(2.93 * (numOfDigits**2) - 164.4*numOfDigits + 2455)

  # comp fBase

  fBase = genFBase(N, fSize)

  # computing kn
  actualK = max(filter(lambda x: x[0] * N % 8 == 1, map(lambda i: (i, knuthSchroeppel(i, N, fBase)), range(1, 103, 2))), key = lambda x: x[1])[0]
  kn = actualK * N
  numOfDigits = int(gp("length(Str({}))".format(kn)))
  T = 0.0268849 * numOfDigits + 0.783929
  M = ceil(386 * (numOfDigits**2) - 23209.3 * numOfDigits + 352768)
  fSize = ceil(2.93 * (numOfDigits**2) - 164.4*numOfDigits + 2455)
  fBase = genFBase(kn, fSize)

  sqrtkn = floor(sqrt(kn))
  sqrt2kn = floor(sqrt(2 * kn))

  sns = []
  for p in fBase[1:]:
    pField = IntegerModRing(p)
    sns.append((pField(kn).nth_root(2)).lift())

  logp = [numerical_approx(log(p)) for p in fBase[1:]]

  pmax = fBase[-1]
  testValue = testFunc(kn, M, pmax, T)

  fullFac = []

  lsAndFacs = dict()
  # comp coeff.

  d = floor(sqrt(sqrt(kn * 2) / M))
  while not (kronecker(d, kn) == 1 and mod(d, 4) == 3):
    d = next_probable_prime(d)

  while len(fullFac) < fSize + 1:
    d = next_probable_prime(d)
    while not (kronecker(d, kn) == 1 and mod(d, 4) == 3):
      d = next_probable_prime(d)
    a = d ** 2
    dRing = IntegerModRing(d)
    #print("a and d")
    b = dRing(kn).nth_root(2).lift()
    b = mod(b - (b**2 - kn) * dRing((2 * b) ** (-1)).lift(), a).lift()
    b = b - a if b % 2 == 0 else b
    c = floor((b ** 2 - kn) / a)

    def q(x):
      return a * x**2 + 2 * b * x + c

    def h(x):
      return  a * x + b

    qs = [0 for i in range(0, 2 * M + 1)]

    termflag = 0

    for i in range(len(fBase) - 1):
      p = fBase[i + 1]
      pRing = IntegerModRing(p)
      if pRing(a) == 0:
        termflag = 1
        break
      root1 = pRing((-b + sns[i]) / a).lift()
      root2 = pRing((-b - sns[i]) / a).lift()
      l1 = root1 + ceil((-M - root1) / p) * p
      l2 = root2 + ceil((-M - root2) / p) * p
      k = 0
      while l1 + k <= M or l2 + k <= M:
        if l1 + k <= M:
          qs[int(l1 + k + M)] += logp[i]
        if l2 + k <= M:
          qs[int(l2 + k + M)] += logp[i]
        k += p

    if termflag == 1:
      continue

    qAndX = enumerate(qs)
    ourPick = filter(lambda x: x[1] > testValue, qAndX) #apply test value

    kysField = IntegerModRing(kn)

    preFac = map(lambda x: (divFac(q(x[0] - M), fBase), (h(x[0] - M), d)), ourPick) # ( (multiplier, vec), (H(x), d) )

    for parvec, sqroot in preFac:
      if parvec[0] == 1: #check if factorisation was full on our fBase
        fullFac.append((parvec[1], sqroot))
      else:
        if parvec[0] in lsAndFacs: #check if there is another entry with the same non-fBase multiplier
          found = lsAndFacs[parvec[0]] # (VEC, ( H(X), d ))
          fullFac.append(([x + y for (x, y) in zip(parvec[1], found[0])], (sqroot[0] * found[1][0], found[1][1] * sqroot[1] * parvec[0]))) # (sumVecs, ( H(x)*H(X), d*d*L ))  
          lsAndFacs.pop(parvec[0])
        else: #if not - add it to the partial factorisation list
          lsAndFacs[parvec[0]] = (parvec[1], sqroot)

    print(numerical_approx(len(fullFac) / (fSize + 1)) * 100)

  GF = IntegerModRing(2)
  vecs = map(lambda x: x[0], fullFac) #fixed
  A = matrix(GF, vecs)
  allSol = A.left_kernel().basis()
  allFacs = set()
  for sol in allSol:
    whatever = filter(lambda x: x[0] == 1, zip(sol, fullFac)) # (1, (VEC, (H(X), AL)))
    
    sumVecs = reduce(lambda xs, ys: [x + y for (x, y) in zip(xs, ys)], map(lambda x: x[1][0], whatever))
    squareVec = map(lambda x: x / 2, sumVecs) #exp vec/2 <=> square root

    soll = mod(product(map(lambda x: x[1][1][0], whatever)), kn) # product H(x)
    alsoR = product(map(lambda x: x[1][1][1], whatever)) #product AL
    solr = mod(alsoR * product(map(lambda x, y: y ** x, squareVec, fBase)), kn) # construct number from factor base and vector of respective powers
    if soll != solr and soll != -solr:
      allFacs.add(gcd(soll + solr, N).lift())
      allFacs.add(gcd(soll - solr, N).lift())
  print(filter(lambda x: 1 < x < N, allFacs))
