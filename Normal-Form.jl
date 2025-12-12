########################################################################
########################################################################
function multiplicative_variables_monomial(M::Vector{Vector{Int64}})
    ## We identify a monomial x_1^(a_1)*...*x_l^(a_l) with the vector [a_1,...,a_l]
    ## We have a vector M = [m_1,...m_n] of monomials, we compute the multiplicative variables for of each m_i in M; the function returns a vector L of integer vectors:
    ## The integer vector L[i] has 1 in position j if x_j is a multiplicative variable for m_i

    ######################################### CHECK: the monomials must all be written with the same number of variables
    t = [length(M[k]) for k in 1:length(M)];
    
    if minimum(t)!=maximum(t)
        return print("Error: the vectors representing the monomials are not all of the same length")
    end

    n = length(M)                           # Number of monomials
    l = length(M[1])                        # Number of indeterminates
    L = [ones(Int64, l) for _ in 1:n];      # Initialize the vectors of multiplicative variables

    if n == 1                               # If there is only one monomial, every variable is a multiplicative variable!
        return L
    end

    a = maximum([M[l][1]] for l in 1:n)[1]  # Maximum exponent of the first variable in all monomials

    if l == 1                               # Only one variable: it is multiplicative for a monomial only if it appears with maximum exponent
        for i in 1:n
            if a > M[i][1]
                L[i][1] = 0;
            end
        end
        return L
    end

    ######################################### Now we have at least two monomials with at least two variables
    for i in 1:n
        ##################################### We check the first variable as before
        if a > M[i][1]
                    L[i][1] = 0;
        end
        
        ##################################### We check the other variables for m_i; for the variable x_j we need to consider the monomials having the same exponents as m_i in the first j-1 variables
        for j in 2:l
            u = M[i][1:j-1];
            S = [v for v in M if v[1:j-1]==u];

            if M[i][j] < maximum(v[j] for v in S)
                L[i][j] = 0;
            end
        end
    end

    return L
end
########################################################################
########################################################################
dominates(v, w) = all(v .<= w)                                                       ## Check the divisibility of the first monomial v by the second monomial w
########################################################################
########################################################################
function decompose(G::Vector{Vector{Int64}}, v::Vector{Int64})                       ## Analogue of Algorithm 2.1.6 in Robertz' book. Here we are assuming a fixed ordering on the variables, namely, x_1<x_2<...<x_l.
    G = filter(x -> !isempty(x), G)             # We delete empty arrays                                                                          
    if isempty(G)                               # If there is no monomial, we return the trivial decomposition
        return [[Int64[],v]]
    elseif maximum(v)==0                        # If there is no variable, we return the trivial decomposition
        return [[g,v] for g in G]
    end

    lengths = length.(G);                       # Check that every monomial is written in the same variables
    if length(Set(lengths)) > 1 || (length(Set(lengths)) == 1 && first(lengths) != length(v))
        return println("Error: the sets of variables used for the monomials and the set of variables do not coincide")
    end

    if length(G)==1                             # Check whether there is exactly one monomial
         return [[g,v] for g in G]
    end

    l = first(lengths);                     # Number of indeterminates
    n = length(G);                          # Number of monomials

    y = findlast(==(1), v);                 # Highest variable appearing
    d = maximum(g[y] for g in G);           # Maximum degree in the highest variable appearing

    w = [v[1:y-1];[0];v[y+1:end]];          # We do not consider the variable y

    ######################################### Initialize the decomposition vectors
    J = [Vector{Int64}[] for _ in 1:d+1]
    K = [[Vector{Int64}[],Vector{Int64}[]] for _ in 1:d+1]

    for i in 1:d+1
        for j in 0:i-1
            for g in G
                if g[y]<=j
                    h = [g[1:y-1];[i-1];g[y+1:end]]
                    push!(J[i],h)
                    J[i] = [v for v in J[i] if !any(u != v && dominates(u, v) for u in J[i])]
                end
            end
        end
        K[i]=decompose(unique(J[i]),w)
    end
    t = zeros(Int64,l);
    t[y]=1;
    K[d+1]=[[a[1],a[2]+t] for a in K[d+1]]
    K = filter(elem -> !any(isempty, elem[1]), K)
    return unique(vcat(K...))
end
########################################################################
########################################################################
function is_Janet_complete_monomial(M::Vector{Vector{Int64}})
    L = multiplicative_variables_monomial(M)     # Multiplicative variables are set to 1
  #  N = [1 .- v for v in L]                     # Non-multiplicative variables are set to 1
    m = length(M)
    for i in 1:m                            
        if minimum(L[i])==1                        # All the variables are multiplicative
            continue
        else
            nv = findall(==(0), L[i])              # Position of non-multiplicative variables
            for j in nv
                w = copy(M[i])
                w[j]=w[j]+1
                if divisibility_check(w,M,L)==true  # Check that the shift of w by a non-multiplicative variable
                                                    # is in the cones of admissible shifts
                    continue
                else
                    return false
                end
            end
        end
    end
    return true
end
########################################################################
########################################################################
function divisibility_check(w::Vector{Int64}, M::Vector{Vector{Int64}}, L::Vector{Vector{Int64}})
    m= length(M)
for i in 1:m
    c = w-M[i]

    pos = max.(sign.(c), 0)
    adm = L[i]
# any(divisibility_check(u, M, multiplicative_variables_monomial(M)) for u in M) MEGLIO
    if !any(x -> x != 0, c) || (minimum(c)>=0 && minimum(adm.-pos)>=0)              # w is in the admissible shifts of M[i]
            return true
        else                                                                        # w is not in the admissible shifts of M[i], but it may be an admissible shift of another monomial
            continue
        end
end
    return false
end
########################################################################
########################################################################
function Janet_completion(M::Vector{Vector{Int64}})
    if is_Janet_complete_monomial(M) == true
        return M
    else
        J = copy(M);
        L = multiplicative_variables_monomial(J)
        non_stop = true;

        while non_stop == true
            non_stop = false
            i = 1;
            while i <= length(J)
                m = J[i]
                nv = findall(==(0), L[i])              # Position of non-multiplicative variables
                for j in nv
                    w = copy(m)
                    w[j] = w[j]+1
                    check = divisibility_check(w, J, L)

                    if check == false
                        push!(J,w)
                        L = multiplicative_variables_monomial(J)     # Multiplicative variables are set to 1
                        non_stop = true
                    end
                end
                i = i+1
            end
        end
    end
    return J
end
########################################################
########################################################
function divisibility_Janet_completion(w::Vector{Int64},J::Vector{Vector{Int64}},L::Vector{Vector{Int64}})
    m= length(M)
    for i in 1:m
        c = w-J[i]
        pos = max.(sign.(c), 0)
        adm = L[i]

        if minimum(c)<0 || minimum(adm.-pos)<0                  # it is not admissible for M[i], but it may be admissible for another
            continue
        else
            return true
        end
    end
        return false
end
########################################################
########################################################
__vtj(dpr::Union{DifferencePolyRing, DifferentialPolyRing}) = dpr.var_to_jet::Dict{elem_type(dpr), Tuple{Int, Vector{Int}}}

function which_shift(p::DifferencePolyRingElem{T}) where T      # Return the shift applied to an elementary symbol in order to obtain the variable p
    if p==leader(p)                                             # Check whether p is a variable
        return map(var -> __vtj(dpr)[var], vars(dpre))[1][2]
    else
        return println("Error: the argument is not a variable")
    end
end

function which_elementary_symbol(p::DifferencePolyRingElem{T}) where T  # return the elementary symbol of the variable p
    if p==leader(p)                                             # check whether p is a variable
        return map(var -> __vtj(dpr)[var], vars(dpre))[1][1]
    else
        return println("Error: the argument is not a variable")
    end
end
###################
###################
function multiplicative_variables(F::Vector{DifferencePolyRingElem{QQFieldElem}}) # Computes the set of multiplicative variables 
                                                                                  # for the leader of each difference polynomial in F
    G = [leader(f) for f in F]
    n = length(F);                                                  # number of difference polynomial in F
    m = n_action_maps(R);                                           # number of elementary symbols in the difference polynomial ring R
    S = [which_shift(l) for l in G];
    return S
    if n == 1
        return elementary_symbols(R)
    end

#    for i in 1:n
#        for j in 1:m
#        if F[1][1]>
#             for j in 1:m
#            
#         end
#    end
#    return M
end











##################
##EXAMPLES

v = 2;                                                                  # number of variables
e = 2;                                                                  # number of morphisms

R, (y_1,y_2) = difference_polynomial_ring(QQ, v, e);
set_ranking!(R, partition=[[0,1],[1,0]], index_ordering_name=:deglex)
n=4;
f_1 = diff_action(y_1, [0,1])^2+1;
f_2 = diff_action(y_1, [2,0])+diff_action(y_2,[0,1]);
f_3 = diff_action(y_1, [0,1])*diff_action(y_2,[0,2]);
f_4 = diff_action(y_1, [1,1])^2-diff_action(y_1,[1,0])^4;
F=[f_1,f_2,f_3,f_4];
mu_1 = [[0,1]]
mu_2 = [[1,0],[0,1]]
mu_3 = [[1,0],[0,1]]
mu_4 = [[0,1]]

f = diff_action(y_2,[1,1])*diff_action(y_2,[0,3])-diff_action(y_1,[2,0]);
g = diff_action(y_1,[3,0])-diff_action(y_2,[0,3])+(diff_action(y_1,[0,1]))^2;

r = f;
b = 1; 

M=[[1, 0, 2, 3],[2, 0, 1, 4], [1, 0, 2, 5], [1, 1, 1, 3], [2, 0, 2, 6], [2, 0, 1, 3]];


f_1
dpr = parent(f_1)