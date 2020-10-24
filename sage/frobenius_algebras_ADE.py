from multiprocessing import Pool
from sage.combinat.root_system.root_system import RootSystem
from sage.groups.perm_gps.permgroup import PermutationGroup
from sage.libs.gap.libgap import libgap
from sage.combinat.free_module import CombinatorialFreeModule
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.modules.free_module import FreeModule
from sage.rings.all import QQ
from sage.categories.magmatic_algebras import MagmaticAlgebras
from progress.bar import Bar


class FrobeniusAlgebraADE(CombinatorialFreeModule):
    def __init__(self, cartan_type, with_unit=True,
                 *args, **kwargs):

        root_system = RootSystem(cartan_type)
        cartan_rank = cartan_type.rank()
        cartan_matrix = root_system.cartan_matrix()
        root_space = root_system.root_space()
        p_roots = list(root_space.positive_roots_by_height())
        roots = p_roots + [-r for r in p_roots]
        roots_ambient = [r.to_ambient() for r in roots]
        dim_ambient = len(roots_ambient[0].to_vector())
        alpha = [r.to_ambient() for r in root_space.simple_roots()]
        num_p_roots = len(p_roots)
        num_roots = len(roots)
        roots_index = {r: i for i, r in enumerate(roots)}

        self._with_unit = with_unit
        self._cartan_type = cartan_type
        self._cartan_rank = cartan_rank
        self._roots = roots
        self._roots_ambient = roots_ambient
        self._ambient_space = root_system.ambient_space()
        self._dim_ambient = dim_ambient
        self._num_p_roots = num_p_roots
        self._num_roots = num_roots

        # Initialize variables needed for product on zero weight space

        # The image of zeta is the space of symmetric (w.r.t kappa) operators.
        # We take zeta(hi,hj) as a basis for this image
        # for i <= j and {h1,...,hn} a basis of simple roots.
        zeta = self._zeta
        basis_zero = [vector(zeta(r, s))
                      for i, r in enumerate(alpha)
                      for s in alpha[i:]]
        self._basis_zero = matrix(basis_zero).transpose()

        # Recall that
        # pi(j_\alpha) = j_\alpha + \sum_\beta \mu_{\alpha,\beta} v_\beta
        # where \mu_\beta is a scalar only depending on |\kappa(\alpha,\beta)|.
        # We compute these \mu_\beta.
        gens = [[(roots_index[r.weyl_action([i])] % num_p_roots) + 1
                 for r in p_roots]
                for i in cartan_type.index_set()]
        W = PermutationGroup(gens)
        elements = [(i+1, j+1) for i in range(num_p_roots)
                    for j in range(num_p_roots)]
        orbits = []
        while len(elements) > 0:
            x = elements.pop()
            orbit = W.orbit(x, action="OnPairs")
            for o in orbit:
                try:
                    elements.remove(o)
                except ValueError:
                    pass
            orbits.append([(o[0]-1, o[1]-1) for o in orbit])
        representatives = [orbit[0] for orbit in orbits]
        num_rep = len(representatives)
        p = [[[0 for i in range(num_rep)]
              for j in range(num_rep)]
             for k in range(num_rep)]
        for k in range(num_rep):
            x = representatives[k][0]
            y = representatives[k][1]
            for z in range(num_p_roots):
                i = 0
                while not (x, z) in orbits[i]:
                    i += 1
                j = 0
                while not (z, y) in orbits[j]:
                    j += 1
                p[i][j][k] = p[i][j][k] + 1
        b = [roots_ambient[r[0]].scalar(roots_ambient[r[1]])
             for r in representatives]
        b = [i*i for i in b]

        # The coefficients for the system of linear equations.
        coefficients = matrix.zero(QQ, num_rep)
        for k in range(num_rep):
            for i in range(num_rep):
                for j in range(num_rep):
                    coefficients[k, i] += p[i][j][k]*b[j]
        for i in range(num_rep):
            coefficients[i, i] += 2
        result = vector([b[k] for k in range(num_rep)])
        sol = coefficients.solve_right(result)

        mu = matrix.zero(QQ, num_p_roots)
        for i in range(num_p_roots):
            for j in range(num_p_roots):
                o = 0
                while not (i, j) in orbits[o]:
                    o += 1
                mu[i, j] = sol[o]
        self._mu = mu

        # Build a matrix where the columns represent the j_\alpha's
        j_list = [vector(zeta(r, r)) for r in roots_ambient[:num_p_roots]]
        self._j = matrix(j_list).transpose()
        self._basis_to_j = self._j.solve_right(self._basis_zero)

        # Initialize variables related to weight-root-spaces
        self._basis_root = []
        for i in range(num_p_roots):
            proj = (1 - QQ(1/2)*self._vect_to_mat(j_list[i]))
            proj_images = proj*(matrix([vector(r) for r in alpha]).transpose())
            basis = (proj_images.column_space().basis()
                     + [roots_ambient[i].to_vector()])
            self._basis_root.append(matrix(basis).transpose())

        # We introduce different types for each pair of weights
        # type 0 : 0 and 0
        # type 1 : 0 and root
        # type 2 : 0 and lambda
        # type 3 : root and -root
        # type 4 : root and root, inner -1
        # type 5 : root and root, inner 0
        # type 6 : root and root, inner > 0
        # type 7 : root and lambda, inner -2
        # type 8 : root and lambda, inner -1 with alpha_lambda
        # type 9 : root and lambda, inner -1 with beta_lambda
        # type 10 : root and lambda, inner > -1
        # type 11 : lambda and -lambda
        # type 12 : lambda and lambda, inner -3
        # type 13 : lambda and lambda, inner -2
        # type 14 : lambda and lambda, inner > -2

        wtype = {}
        wsum = {}

        c = {}


        Lambda_0 = []
        Lambda_0_ambient = []
        Lambda_0_index = {}
        chosen_pairs = []
        e_lambda = []

        num_Lambda_0 = 0
        n_lambda = []

        root_weightindex = self._root_weightindex
        lambda_weightindex = self._lambda_weightindex
        negative_rootindex = self._negative_rootindex

        for i, r in enumerate(p_roots):
            wi = root_weightindex(i)
            wni = root_weightindex(num_p_roots + i)
            for j in range(i, num_p_roots):
                wj = root_weightindex(j)
                wnj = root_weightindex(num_p_roots + j)
                s = p_roots[j]
                scalar = roots_ambient[i].scalar(roots_ambient[j])
                if scalar == -2:
                    wtype[(wi, wj)] = 3
                    wsum[(wi, wj)] = 0
                    wtype[(wj, wni)] = 6
                    wtype[(wi, wnj)] = 6
                    wtype[(wni, wnj)] = 3
                    wsum[(wni, wnj)] = 0
                elif scalar == -1:
                    rs = r + s
                    isum = root_weightindex(roots_index[rs])
                    wtype[(wi, wj)] = 4
                    wsum[(wi, wj)] = isum
                    wtype[(wj, wni)] = 6
                    wtype[(wi, wnj)] = 6
                    wtype[(wni, wnj)] = 4
                    wsum[(wni, wnj)] = (num_p_roots + isum)

                    x, y = rs.extraspecial_pair()
                    ix = roots_index[x]
                    iy = roots_index[y]
                    if (ix, iy) == (i, j):
                        if (ix, iy) not in c:
                            if (sum(x.coefficients()) == sum(y.coefficients())
                                    and str(x) > str(y)):
                                iy, ix = ix, iy
                            c[(ix, iy)] = -1
                            c[(iy, ix)] = 1
                    elif (roots_ambient[j].scalar(roots_ambient[ix]) == 1):
                        ismx = roots_index[s-x]
                        iymr = roots_index[y-r]
                        c[(i, j)] = -c[(ix, ismx)]*c[(i, iymr)]
                        c[(j, i)] = -c[(i, j)]
                    else:
                        irmx = roots_index[r-x]
                        iyms = roots_index[y-s]
                        c[(i, j)] = c[(ix, irmx)] * c[(j, iyms)]
                        c[(j, i)] = -c[(i, j)]
                    ni = negative_rootindex(i)
                    nj = negative_rootindex(j)
                    c[(ni, nj)] = -c[(i, j)]
                    c[(nj, ni)] = c[(i, j)]

                elif scalar == 0:
                    wtype[(wi, wj)] = 5
                    wtype[(wj, wni)] = 5
                    wtype[(wi, wnj)] = 5
                    wtype[(wni, wnj)] = 5

                    e_lambda_part = (j_list[i] + j_list[j])
                    e_lambda_part = self._mat_to_basis(e_lambda_part)

                    lam1 = r + s
                    try:
                        ind_p = Lambda_0_index[lam1]
                        ind_n = Lambda_0_index[-lam1]

                        e_lambda[ind_p] += e_lambda_part
                        e_lambda[ind_n] += e_lambda_part

                        n_lambda[ind_p] += 1
                        n_lambda[ind_n] += 1
                    except KeyError:
                        Lambda_0_index[lam1] = num_Lambda_0
                        ind_p = num_Lambda_0
                        num_Lambda_0 += 1
                        Lambda_0.append(lam1)
                        lam1_ambient = (roots_ambient[i]
                                        + roots_ambient[j])
                        Lambda_0_ambient.append(lam1_ambient)

                        Lambda_0_index[-lam1] = num_Lambda_0
                        ind_n = num_Lambda_0
                        num_Lambda_0 += 1
                        Lambda_0.append(-lam1)
                        Lambda_0_ambient.append(-lam1_ambient)
                        chosen_pairs.append((i, j))
                        chosen_pairs.append((i + num_p_roots, j + num_p_roots))
                        e_lambda.append(e_lambda_part)
                        e_lambda.append(e_lambda_part)

                        n_lambda.append(1)
                        n_lambda.append(1)
                    wsum[(wi, wj)] = lambda_weightindex(ind_p)
                    wsum[(wni, wnj)] = lambda_weightindex(ind_n)

                    lam2 = - r + s
                    try:
                        ind_p = Lambda_0_index[lam2]
                        ind_n = Lambda_0_index[-lam2]

                        e_lambda[ind_p] += e_lambda_part
                        e_lambda[ind_n] += e_lambda_part

                        n_lambda[ind_p] += 1
                        n_lambda[ind_n] += 1
                    except KeyError:
                        Lambda_0_index[lam2] = num_Lambda_0
                        ind_p = num_Lambda_0
                        num_Lambda_0 += 1
                        Lambda_0.append(lam2)
                        lam2_ambient = (-roots_ambient[i]
                                        + roots_ambient[j])
                        Lambda_0_ambient.append(lam2_ambient)

                        Lambda_0_index[-lam2] = num_Lambda_0
                        ind_n = num_Lambda_0
                        num_Lambda_0 += 1
                        Lambda_0.append(-lam2)
                        Lambda_0_ambient.append(-lam2_ambient)

                        chosen_pairs.append((j, i + num_p_roots))
                        chosen_pairs.append((i, j + num_p_roots))

                        e_lambda.append(e_lambda_part)
                        e_lambda.append(e_lambda_part)

                        n_lambda.append(1)
                        n_lambda.append(1)
                    wsum[(wj, wni)] = lambda_weightindex(ind_p)
                    wsum[(wi, wnj)] = lambda_weightindex(ind_n)

                elif scalar == 1:
                    wtype[(wi, wj)] = 6
                    wtype[(wni, wnj)] = 6
                    isum = root_weightindex(roots_index[-r + s])
                    wtype[(wj, wni)] = 4
                    wsum[(wj, wni)] = isum
                    wtype[(wi, wnj)] = 4
                    wsum[(wi, wnj)] = num_p_roots + isum

                    x, y = s-r, r
                    ix = roots_index[x]
                    iy = roots_index[y]
                    ni = negative_rootindex(i)
                    nj = negative_rootindex(j)
                    cte = c[(ix, iy)]
                    c[(ni, j)] = -cte
                    c[(j, ni)] = cte
                    c[(i, nj)] = cte
                    c[(nj, i)] = -cte

                elif scalar == 2:
                    wtype[(wi, wj)] = 6
                    wtype[(wni, wnj)] = 6
                    wtype[(wj, wni)] = 3
                    wsum[(wj, wni)] = 0
                    wtype[(wi, wnj)] = 3
                    wsum[(wi, wnj)] = 0

        wtype[(0, 0)] = 0
        wsum[(0, 0)] = 0

        for i in range(num_roots):
            wi = root_weightindex(i)
            wtype[(0, wi)] = 1
            wsum[(0, wi)] = wi

        for i in range(num_Lambda_0):
            wi = lambda_weightindex(i)
            wtype[(0, wi)] = 2
            wsum[(0, wi)] = wi

        for i, r in enumerate(roots):
            wi = root_weightindex(i)
            for j in range(num_Lambda_0):
                wj = lambda_weightindex(j)
                lam = Lambda_0[j]
                lam_ambient = Lambda_0_ambient[j]
                scalar = roots_ambient[i].scalar(lam_ambient)
                if scalar == -2:
                    wtype[(wi, wj)] = 7
                    isum = roots_index[lam+r]
                    wsum[(wi, wj)] = root_weightindex(isum)
                elif scalar == -1:
                    r0 = roots_ambient[chosen_pairs[j][0]]
                    if roots_ambient[i].scalar(r0) == -1:
                        wtype[(wi, wj)] = 8
                    else:
                        wtype[(wi, wj)] = 9
                    isum = Lambda_0_index[lam+r]
                    wsum[(wi, wj)] = lambda_weightindex(isum)
                else:
                    wtype[(wi, wj)] = 10

        for i, lam1 in enumerate(Lambda_0):
            e_lambda[i] = (QQ(1/(4*n_lambda[i])) * e_lambda[i])
            wi = lambda_weightindex(i)
            lam1_ambient = Lambda_0_ambient[i]
            for j in range(i, num_Lambda_0):
                wj = lambda_weightindex(j)
                lam2 = Lambda_0[j]
                lam2_ambient = Lambda_0_ambient[j]
                scalar = lam1_ambient.scalar(lam2_ambient)
                if scalar == -4:
                    wtype[(wi, wj)] = 11
                    wsum[(wi, wj)] = 0
                elif scalar == -3:
                    wtype[(wi, wj)] = 12
                    isum = roots_index[lam1 + lam2]
                    wsum[(wi, wj)] = root_weightindex(isum)
                elif scalar == -2:
                    wtype[(wi, wj)] = 13
                    isum = Lambda_0_index[lam1 + lam2]
                    wsum[(wi, wj)] = lambda_weightindex(isum)
                else:
                    wtype[(wi, wj)] = 14

        self._type = wtype
        self._sum = wsum
        self._c = c
        self._Lambda_0 = Lambda_0
        self._num_lambda = len(Lambda_0)
        self._Lambda_0_index = Lambda_0_index
        self._chosen_pairs = chosen_pairs
        self._e_lambda = e_lambda

        # Needed if with_unit=False
        if not with_unit or True:
            sum_j = sum((self._basis_zero.solve_right(self._j)).columns())
            projected_basis_zero = []
            bil = self._bil_zero_zero
            scal = bil(sum_j, sum_j)
            for b in FreeModule(QQ, len(basis_zero)).basis():
                projection = b - bil(sum_j, b)/scal*sum_j
                projected_basis_zero.append(self._basis_zero*projection)
            self._projected_basis_zero = (matrix(projected_basis_zero)
                                          .transpose())

        # Initialize underlying CombinatorialFreeModule
        ind_basis_zero = [f"h_{i}h_{j}" for i in range(cartan_rank)
                          for j in range(i, cartan_rank)]
        if not with_unit:
            ind_basis_zero.pop()
        self._dim_zero = len(ind_basis_zero)
        ind_basis_root = [f"e_{i}_{j}" for i in range(num_roots)
                          for j in range(cartan_rank-1)]
        self._dim_root = len(ind_basis_root)
        ind_basis_lambda = [f"x_{i}" for i in range(num_Lambda_0)]
        self._dim_lambda = len(ind_basis_lambda)
        ind_basis = ind_basis_zero + ind_basis_root + ind_basis_lambda

        cat = MagmaticAlgebras(QQ).FiniteDimensional().WithBasis()
        CombinatorialFreeModule.__init__(self, QQ, ind_basis,
                                         category=cat,
                                         *args, **kwargs)

    # The map
    # zeta : H x H -> Hom(H,H) : (h1,h2) |->
    # [h |-> 1/2(kappa(h,h1)h2 + kappa(h,h2)h1]
    # where kappa is the Killing form.
    def _zeta(self, h1, h2):
        v1 = h1.to_vector()
        v2 = h2.to_vector()
        return QQ(1/2)*(v1.column()*v2.row()
                        + v2.column()*v1.row())

    def _vect_to_mat(self, v):
        n = self._dim_ambient
        return matrix(n, n, v)

    def _basis_to_mat(self, v):
        n = self._dim_ambient
        return matrix(n, n, self._basis_zero*v)

    def _mat_to_basis(self, mat):
        return self._basis_zero.solve_right(vector(mat))

    def from_dict(self, d):
        result = vector(self.base_ring(), self.dimension())
        for i in d.keys():
            if i == 0:
                result[:self._dim_zero] = d[i]
            elif i < 1 + self._num_roots:
                result[self._root_slice(i-1)] = d[i]
            else:
                result[self._lambda_slice(i-1-self._num_roots)] = d[i]
        return self.from_vector(result)

    def _root_slice(self, i):
        start = self._dim_zero + (self._cartan_rank - 1)*i
        stop = start + self._cartan_rank - 1
        return slice(start, stop)

    def _lambda_slice(self, i):
        start = self._dim_zero + self._dim_root + i
        return slice(start, start + 1)

    def _root_weightindex(self, i):
        return 1 + i

    def _lambda_weightindex(self, i):
        return 1 + self._num_roots + i

    def _weight_rootindex(self, i):
        return i - 1

    def _weight_lambdaindex(self, i):
        return i - 1 - self._num_roots

    def _mult_zero_zero(self, v, w):
        j = self._j
        basis_to_j = self._basis_to_j
        mu = self._mu
        # Write as linear combination of the j_\alpha's
        v_prime = basis_to_j*v
        w_prime = basis_to_j*w
        # Write pi_A(v)-v as linear comination of the v_\alpha's
        vv = mu*v_prime
        wv = mu*w_prime
        # Compute component in J
        vj = self._vect_to_mat(j*(v_prime-vv))
        wj = self._vect_to_mat(j*(w_prime-wv))
        prod_j = QQ(1/2)*vj*wj
        prod_j = vector(prod_j + prod_j.transpose())
        # Compute (half of) the component in Z
        prod_z = vector(vv[i]*wv[i] for i in range(self._num_p_roots))
        # Compute the projection of the product (as matrices)
        prod = prod_j+j*prod_z
        # Return as linear combination of basis elements
        return self._mat_to_basis(prod)

    def _bil_zero_zero(self, v, w):
        j = self._j
        basis_to_j = self._basis_to_j
        mu = self._mu
        # Write as linear combination of the j_\alpha's
        v_prime = basis_to_j*v
        w_prime = basis_to_j*w
        # Write pi_A(v)-v as linear comination of the v_\alpha's
        vv = mu*v_prime
        wv = mu*w_prime
        # Compute bilinear form in J
        vj = self._vect_to_mat(j*(v_prime-vv))
        wj = self._vect_to_mat(j*(w_prime-wv))
        bil_j = (vj*wj).trace()
        # Compute bilinear form in Z
        bil_z = 2*vv*wv
        # Return sum
        return bil_j + bil_z

    # Project a vector onto orthogonal complement of i-th root
    def _proj_root(self, i, v):
        return (self._basis_root[i % self._num_p_roots]
                .solve_right(vector(v))[:self._cartan_rank-1])

    # Embed vector in orthogonal complement of i-th root in root space
    def _embed_root(self, i, v):
        coord = list(self._basis_root
                     [i % self._num_p_roots]
                     [:, :self._cartan_rank-1]
                     * v)
        return self._ambient_space(coord)

    def _negative_rootindex(self, i):
        num_p_roots = self._num_p_roots
        if i < num_p_roots:
            return i + num_p_roots
        else:
            return i - num_p_roots

    def _f(self, i, j):
        roots = self._roots
        negative_rootindex = self._negative_rootindex
        c = self._c
        lam = roots[i] + roots[j]
        lam_index = self._Lambda_0_index[lam]
        cp = self._chosen_pairs[lam_index]
        if cp[0] in [i, j]:
            return 1
        else:
            return (- c[(i, negative_rootindex(cp[0]))]
                    * c[(j, negative_rootindex(cp[1]))])

    # Symmetrized version of type dictionary
    def _type_sym(self, i, j):
        if i < j:
            return self._type[(i, j)]
        else:
            return self._type[(j, i)]

    # Symmetrized version of sum dictionary
    def _sum_sym(self, i, j):
        if i < j:
            return self._sum[(i, j)]
        else:
            return self._sum[(j, i)]

    # Action of e_\alpha for \alpha the i-th root
    def _lie_action_help(self, i, j, v):
        wi = self._root_weightindex(i)
        t = self._type_sym(wi, j)
        if t == 6 or t == 10:
            return -1, 0
        elif t == 1:
            vmat = self._basis_to_mat(v)
            image = vmat*(self._roots_ambient[i].to_vector())
            result = -2*self._proj_root(i, image)
            return wi, result
        elif t == 3:
            root_index = self._weight_rootindex(j)
            mat = self._zeta(self._roots_ambient[i],
                             self._embed_root(root_index, v))
            result = self._mat_to_basis(mat)
            return 0, result
        elif t == 4:
            root_index = self._weight_rootindex(j)
            embed = self._embed_root(root_index, v)
            sum_index = self._sum_sym(wi, j)
            res = (embed
                   + embed.scalar(self._roots_ambient[i])
                   * self._roots_ambient[root_index])
            proj = self._proj_root(self._weight_rootindex(sum_index), res)
            return sum_index, self._c[(i, root_index)]*proj
        elif t == 5:
            root_index = self._weight_rootindex(j)
            embed = self._embed_root(root_index, v)
            scalar = self._roots_ambient[i].scalar(embed)
            return (self._sum_sym(wi, j),
                    vector([-scalar * self._f(i, root_index)]))
        elif t == 7:
            sum_index = self._sum[(wi, j)]
            root_index = self._weight_rootindex(sum_index)
            proj = v[0]*self._proj_root(root_index, self._roots_ambient[i])
            return sum_index, self._f(root_index,
                                      self._negative_rootindex(i))*proj
        elif t == 8:
            lambda_index = self._weight_lambdaindex(j)
            cp = self._chosen_pairs[lambda_index]
            wcp0 = self._root_weightindex(cp[0])
            root_index = self._weight_rootindex(self._sum_sym(wcp0, wi))
            sum_index = self._sum[(wi, j)]
            result = self._c[(i, cp[0])] * self._f(root_index, cp[1])
            return sum_index, result*v
        elif t == 9:
            lambda_index = self._weight_lambdaindex(j)
            cp = self._chosen_pairs[lambda_index]
            wcp1 = self._root_weightindex(cp[1])
            root_index = self._weight_rootindex(self._sum_sym(wcp1, wi))
            sum_index = self._sum[(wi, j)]
            result = self._c[(i, cp[1])] * self._f(cp[0], root_index)
            return sum_index, result*v

    def _lie_action(self, i, v):
        v_dict = self._vector_to_dict(v)
        res_dict = {}
        for j in v_dict.keys():
            ires, res = self._lie_action_help(i, j, v_dict[j])
            self._add_comp(res_dict, ires, res)
        return self._dict_to_vector(res_dict)

    def _add_comp(self, v_dict, i, v):
        if (i != -1) and (not v.is_zero()):
            try:
                old_value = v_dict[i]
                new_value = old_value + v
                if new_value.is_zero():
                    del v_dict[i]
                else:
                    v_dict[i] = new_value
            except KeyError:
                v_dict[i] = v

    # Multiply vector of weight i with vector of weight j
    def _mult_help(self, i, v, j, w):
        if i > j:
            return self._mult_help(j, w, i, v)
        t = self._type[(i, j)]
        if t in [6, 10, 14]:
            return -1, 0
        elif t == 0:
            return 0, self._mult_zero_zero(v, w)
        elif t == 1:
            rj = self._weight_rootindex(j)
            nrj = self._negative_rootindex(rj)
            _, res = self._lie_action_help(nrj, j, w)
            res = self._mult_zero_zero(v, res)
            s, res = self._lie_action_help(rj, 0, res)
            return s, QQ(1/2)*res
        elif t == 2:
            lamj = self._weight_lambdaindex(j)
            return j, self._bil_zero_zero(v, self._e_lambda[lamj])*w
        elif t in [3, 4, 5, 7, 8, 9]:
            ri = self._weight_rootindex(i)
            nri = self._negative_rootindex(ri)
            _, nri_v = self._lie_action_help(nri, i, v)
            _, res1 = self._mult_help(0, nri_v, j, w)
            _, res1 = self._lie_action_help(ri, j, res1)
            s, ri_w = self._lie_action_help(ri, j, w)
            _, res2 = self._mult_help(0, nri_v, s, ri_w)
            return s, QQ(1/2)*(res1-res2)
        elif t in [11, 12, 13]:
            lami = self._weight_lambdaindex(i)
            ai = self._chosen_pairs[lami][0]
            nai = self._negative_rootindex(ai)
            inew, vnew = self._lie_action_help(nai, i, v)
            s1, res1 = self._mult_help(inew, vnew, j, w)
            s2, res2 = self._lie_action_help(ai, j, w)
            if s1 != -1:
                s1, res1 = self._lie_action_help(ai, s1, res1)
                if s2 != -1:
                    s2, res2 = self._mult_help(inew, vnew, s2, res2)
                    return s1, QQ(1/2)*(res1 - res2)
                else:
                    return s1, QQ(1/2)*res1
            else:
                # s2 must be different from -1
                s2, res2 = self._mult_help(inew, vnew, s2, res2)
                return s2, QQ(-1/2)*res2

    def product(self, v, w):
        v_dict = v.to_dict()
        w_dict = w.to_dict()
        if not self._with_unit:
            v_dict = self._basis0_to_basis(v_dict)
            w_dict = self._basis0_to_basis(w_dict)
        mult_help = self._mult_help
        proc = []
        with Pool() as pool:
            for i in v_dict.keys():
                for j in w_dict.keys():
                    proc.append(pool.apply_async(mult_help,
                                                 (i, v_dict[i], j, w_dict[j])))
            pool.close()
            pool.join()
        res_dict = {}
        add_comp = self._add_comp
        for p in proc:
            ires, res = p.get()
            add_comp(res_dict, ires, res)
        if not self._with_unit:
            res_dict = self._basis_to_basis0(res_dict)
        return self.from_dict(res_dict)

    def _basis0_to_basis(self, d):
        if 0 in d:
            embed = self._projected_basis_zero[:, :-1]*d[0]
            d[0] = self._mat_to_basis(embed)
        return d

    def _basis_to_basis0(self, d):
        if 0 in d:
            proj = self._projected_basis_zero*d[0]
            coord = self._projected_basis_zero[:, :-1].solve_right(proj)
            d[0] = coord
        return d

    def _adjoint(self, v, with_bar=False):
        if with_bar:
            bar = Bar("Computing...",
                      suffix='Elapsed: %(elapsed)d s - ETA: %(eta)d s',
                      max=self.dimension())
        res = []
        for w in self.b:
            res.append(self._mult_(v, w))
            if with_bar:
                bar.next()
        return matrix(res).transpose()

    def _repr_(self):
        return "Frobenius algebra for cartan type %s" % \
                self._cartan_type

    # Class for elements of Frobenius algebras
    class Element(CombinatorialFreeModule.Element):

        def to_dict(self):
            v = self.to_vector()
            p = self.parent()
            result = {}
            v0 = v[:p._dim_zero]
            if not v0.is_zero():
                result[0] = v0
            root_slice = p._root_slice
            root_weightindex = p._root_weightindex
            for i in range(p._num_roots):
                vr = v[root_slice(i)]
                if not vr.is_zero():
                    result[root_weightindex(i)] = vr
            lambda_slice = p._lambda_slice
            lambda_weightindex = p._lambda_weightindex
            for i in range(p._num_lambda):
                vl = v[lambda_slice(i)]
                if not vl.is_zero():
                    result[lambda_weightindex(i)] = vl
            return result

        def adjoint(self):
            d = self.to_dict()
            p = self.parent()
            if not p._with_unit:
                d = p._basis0_to_basis(d)
            prod = p._mult_help
            res = []
            with Pool() as pool:
                for b in FreeModule(QQ, p._dim_zero).basis():
                    if not p._with_unit:
                        b = p._basis0_to_basis({0: b})[0]
                    res_parts = []
                    for i in d.keys():
                        res_parts.append(pool.apply_async(prod,
                                                          (i, d[i], 0, b)))
                    res.append(res_parts)

                for b in FreeModule(QQ, p._cartan_rank-1).basis():
                    for j in range(p._num_roots):
                        res_parts = []
                        for i in d.keys():
                            res_part = pool.apply_async(prod,
                                                        (i, d[i], j+1, b))
                            res_parts.append(res_part)
                        res.append(res_parts)

                b = vector([1])
                for j in range(p._num_lambda):
                    res_parts = []
                    for i in d.keys():
                        jw = j + p._num_roots + 1
                        res_part = pool.apply_async(prod, (i, d[i], jw, b))
                        res_parts.append(res_part)
                    res.append(res_parts)
                pool.close()
                pool.join()
            add_comp = p._add_comp
            from_dict = p.from_dict
            basis_to_basis0 = p._basis_to_basis0
            ad = []
            for r in res:
                res_dict = {}
                for part in r:
                    ind, vec = part.get()
                    add_comp(res_dict, ind, vec)
                if not p._with_unit:
                    res_dict = basis_to_basis0(res_dict)
                ad.append(from_dict(res_dict).to_vector())
            return matrix(ad).transpose()
