"""coffee.py
This program checks if given (x,y) [positive integers], you can get to
(0,1) using the coffee can rules.

The boolean variables have either of the following names:
- '_black_' + str(val) + '_' + str(i)
  where val is a nonnegative integer <= x (here + is a string concat)
  and i is a nonnegative integer < n (n is the bound for bounded model checking)
- '_white_' + str(val) + '_' + str(i)
  where val is a nonnegative integer <= y (here + is a string concat)
  and i is a nonnegative integer < n (n is the bound for bounded model checking)
"""

from z3 import *

def bean(colour,val,step):
    """
    Return the variable (colour,val,step).
    """
    assert isinstance(colour,str), 'bean: colour is not a str'
    assert colour == 'black' or colour == 'white', 'bean: invalid colour'
    assert isinstance(val,int), 'bean: val is not an int'
    assert isinstance(step,int), 'bean: step is not an int'

    return Bool('_'+colour+'_' + str(val) + '_' + str(step))

def init(x,y):
    """
    Return a conjunct for the initial state
    """
    return And( bean('black',x,0), bean('white',y,0) )

def final(x,y,n):
    """
    Return a conjunct for the final state
    """
    return And( bean('black',x,n), bean('white',y,n) )

def uniqueVal(x0,y0,n):
    """
    Return a conjunct saying unique value for n. The start values
    for (x,y) are (x0,y0).
    """
    List1 = [ Implies( bean('black',x,n), Not(bean('black',x1,n )) ) \
                for x  in range(0,x0+y0+1) \
                    for x1 in range(0,x0+y0+1) if x1 > x ]
    List2 = [ Implies( bean('white',y,n), Not(bean('white',y1,n )) ) \
                for y in range(0,x0+y0+1) \
                    for y1 in range(0,x0+y0+1) if y1 > y ]
    List1.extend(List2)
    return And(List1)

def uniqueVals(x0,y0,n0):
    """
    Same as uniqueVal but across n with range(0,n0+1)
    """
    return And([ uniqueVal(x0,y0,i) for i in range(0,n0+1) ])

def nextStep(x,y,n):
    """
    Return that if you are in (x,y,n), then next step you'll be in
    (x+a,y+b,n+1), where a and b are determined using the coffee can rules.
    """
    black0 = bean('black',x,n)
    white0 = bean('white',y,n)
    NextConfs = []
    NextPoints = []
    # Notice that the following conditionals are exclusive
    if y >= 2:
        NextPoints.append((x+1, y-2))
        NextConfs.append(And( bean('black',x+1,n+1), bean('white',y-2,n+1) ))
    if x >= 2 or (x >= 1 and y >= 1):
        NextPoints.append((x-1, y))
        NextConfs.append(And( bean('black',x-1,n+1), bean('white',y,n+1) ))
    if (x == 1 and y == 0) or (x == 0 and y == 1):
        NextConfs.append(And(black0,white0))

    return Implies( And(black0,white0), Or(NextConfs) ), NextPoints

def allTransitions(x0,y0,n0):
    """
    Return all transitions across all n with initial state
    """
    # Note: try to improve this, i.e., make this formula smaller
    transitions_optimised = []
    next_transitions = [(x0, y0)]
    n = 0
    while next_transitions and n < n0 + 1:
        next_transitions_new = []
        for x, y in next_transitions:
            if x in range(0, x0 + y0 + 1) and y in range(0, x0 + y0 + 1):
                next_step, next_transitions_new = nextStep(x, y, n)
                transitions_optimised.append(next_step)
        next_transitions = next_transitions_new
        n += 1
    return And(transitions_optimised)

def Gries(x,y,n):
    """
    This function returns a boolean formula encoding bounded model
    checking of Gries(x,y) for n steps.
    """
    assert x+y >= 1, 'Gries: x+y is < 1'
    assert n >= 0, 'Gries: n is < 0'

    return And([init(x,y),final(0,1,n),allTransitions(x,y,n),uniqueVals(x,y,n)])

def main():
    x = 10
    y = 10
    n = x+y-1

    s = Solver()
    print 'Constructing formula'
    s.add( Gries(x,y,n) )
    print 'Solving the formula'
    # Note that sat and unsat below are constants defined in z3
    if s.check() == sat:
        print 'Last bean can be white'
        print s.model()
    else:
        print 'Last bean cannot be white'


if __name__ == '__main__':
    main()
