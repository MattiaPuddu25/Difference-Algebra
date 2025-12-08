R, (y_1,y_2) = difference_polynomial_ring(QQ, 2, 2);
set_ranking!(R, partition=[[0,1],[1,0]], index_ordering_name=:deglex)
n=4
f_1 = diff_action(y_1, [0,1])^2+1;
f_2 = diff_action(y_1, [2,0])+diff_action(y_2,[0,1]);
f_3 = diff_action(y_1, [0,1])*diff_action(y_2,[0,2]);
f_4 = diff_action(y_1, [1,1])^2-diff_action(y_1,[1,0])^4;

mu_1 = [[0,1]]
mu_2 = [[1,0],[0,1]]
mu_3 = [[1,0],[0,1]]
mu_4 = [[0,1]]

f = diff_action(y_2,[1,1])*diff_action(y_2,[0,3])-diff_action(y_1,[2,0]);
g = diff_action(y_1,[3,0])-diff_action(y_2,[0,3])+(diff_action(y_1,[0,1]))^2;

r = f;
b = 1;


function multiplicative_variables(F::Vector{DifferencePolyRingElem{QQFieldElem}})
    n = 4   # The function n_action_maps is not present!
    for i in 1:4
        
    end
end
