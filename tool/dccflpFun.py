# -*- coding: utf-8 -*-
# An unified algorithm framework for the Facility Location, Allocation and Service Area Problems.
# yfkong@henu.edu.cn, Apr.,2021
# to solve problems such as:
# 1 GAP,SAP
# 2 SSCFLP, SSCKFLP, CFLSAP, CKFLSAP
# 3 PMP/CPMP
# 4 PDP
# 5 Eaqul-capacity PMP (ECPMP)
# 6 SSCFLP_R:CFLP with covering radius and covering percentage

import copy
import math
import os
import random
import tempfile
import time
import arcpy
# ArcGIS
has_arcpy = 1
# mip solver
mip_solvers = []  # MIP solvers supported
mip_solver = ''  # MIP solver, "cplex", "cbc" or ""
mip_file_path = tempfile.gettempdir()
os.chdir(mip_file_path)  # used in arcgis
try:
    import cplex
    # mip_solvers.append('cplex')
except:
    pass
try:
    import pulp

    s = pulp.apis.GUROBI_CMD()
    if not s.available():
        pass
    else:
        mip_solvers.append('gurobi')
    s = pulp.apis.cplex_api.CPLEX_CMD()
    if not s.available():
        pass
    else:
        mip_solvers.append('cplex')
    s = pulp.apis.COIN_CMD()
    if not s.available():
        pass
    else:
        mip_solvers.append('cbc')
except:
    pass
if len(mip_solvers) > 0: mip_solver = mip_solvers[0]

# constant
MAXNUMBER = 1.0e+20
MINNUMBER = 1.0e-10
# instance info
nodes = []
nodes_std = []  # for homoDP only
weight_features = []  # for homoDP only
num_units = -1
nodedij = []
nodedik = []  # weighted cost from i to k, =nodedij*nodes[][3]
nodendij = []  # network distance
node_neighbors = []
facility_neighbors = []
total_pop = 0
avg_pop = 0
total_supply = 0
all_units_as_candadate_locations = 0
facilityCandidate = []
facility_inclusion_list = []
facilityCapacity = []
facilityCost = []
num_facilityCandidate = -1
num_districts = -1  # number of service areas/facilities
avg_dis_min = 1.0
potential_facilities = []
NearFacilityList = []
nearCustomer = []
nearCustomers = []
geo_instance = 1
pmp_I_eaquls_J = 1

# parameters for districting
location_problem = 1
max_num_facility = 999
adaptive_number_of_facilities = 1
fixed_cost_obj = 1
spatial_contiguity = 1  # 0 no, 1 yes, 2 yes with multi-parts
spatial_contiguity_minimum_percentage = 5
pop_dis_coeff = 10000.0  # used in the objective function
pop_deviation = 0.00  # for pdp, 5%
cflp_max_service_radius = 10000.0
cflp_service_radius_preference = 10000.0
cflp_min_service_coverage_percentage = 100.0

# current solution
centersID = []
node_groups = []
district_info = []  # [[0,0,0.0] for x in range(num_districts)] # solution
objective_overload = 0
obj_balance = MAXNUMBER
objective = MAXNUMBER
objective_fcost = MAXNUMBER
biobjective = MAXNUMBER
objective_supply = 0.0

given_solution = 0  # reserved
all_solutions = []

# best solution in each start
best_solution = []  # node_groups[:]
best_centersID = []
best_biobjective = MAXNUMBER
best_objective = MAXNUMBER
best_objective_overload = MAXNUMBER
best_objective_fcost = MAXNUMBER
# global best solution
# best_centers_global=[]
best_solution_global = []
best_centersID_global = []
best_biobjective_global = MAXNUMBER
best_objective_global = MAXNUMBER
best_objective_fcost_global = MAXNUMBER
best_overload_global = MAXNUMBER

# search statistics
time_check = 0
time_check_edge_unit = 0
time_spp = 0.0
time_update_centers = 0.0
time_op = [0.0 for x in range(10)]
time_ruin_recreate = [0.0 for x in range(10)]
time_location = [0.0 for x in range(10)]
time_pmp_re_location = 0.0
time_Whitaker = 0.0
time_repair = 0
count_op = [0.0 for x in range(10)]
check_count = 0
improved = 0
move_count = 0

# search history
region_pool = []
pool_index = []

# local search
acceptanceRule = "hc"  # solver name
assignment_operators_selected = [0, 1]  # 0 one-unit move, 1 two-unit move, 2 three-unit move
location_operators_selected = [0, 1, 2, 3, 4]  # 0 swap, 1 drop, 2 add, 3 add+drop, 4 me
ruin_oprators = [0, 1, 2, 3, 4]  # ruin0, ruin1, 9 mip assign
multi_start_count = 6  # population size for GA, ILS, VNS, LIS+VND
initial_solution_method = 0  # 0 construction, 1 LP
assign_method = 0  # not used
assign_or_Location_search_method = 0
large_facility_cost = 0
maxloops = 1000
max_loops_solution_not_improved = -1
SA_maxloops = 100  # maximum number of search loops for GA
SA_temperature = 1.0
op_random = 1  # operators used sequentially (0) or randomly(1)
last_loop_obj = 0.0
ruin_percentage = 20
mainloop = 0
mutation_rate = 0.01
cross_methods = -1
adj_pop_loops = 5000
solution_similarity_limit = 10.0

# mip modelling for initial solution, spp and full model
is_spp_modeling = 1  # 0 no spp modelling, 1 modelling at the end, 2 modelling in case of local optimum
linear_relaxation = 0
spp_loops = 400
solver_time_limit = 7200  # used for mip modeling
solver_mipgap = 0.000000000001
solver_message = 0
heuristic_time_limit = 300
seed = random.randint(0, 10000)
random.seed(seed)
locTabuLength = 100  # nf*psize
locTabuList = []
locTabuList2 = []


# 函数内调用的函数
def arcpy_print(s):
    import arcpy as arc
    arc.AddMessage(s)


# read network distance
def readdistance(dfile):
    global nodedij
    global nodedik
    arcpy_print("reading distances ...")
    try:
        f = open(dfile)
        # if len(nodedij)!=num_units:
        nodedij = [[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
        line = f.readline()
        line = f.readline()
        readsuccess = 1
        did = [x[4] for x in nodes]
        fid = [x[4] for x in nodes if x[5] > 0]
        arcpy_print(fid)
        while line:
            items = line.split(',')
            if len(items) <= 2:
                items = line.split('\t')
            id1 = int(items[1])
            id2 = int(items[2])
            if id2 not in fid:
                line = f.readline()
                continue
            idx1 = did.index(id1)
            idx2 = fid.index(id2)
            nodedij[idx1][idx2] = float(items[3])
            line = f.readline()
        f.close()
        find_NearFacilityList(num_districts)
        find_near_customer()
        nodedik = [[nodedij[y][x] * nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
        return 1
    except:
        arcpy_print("Cannot read the distance data file!!!{0}".format(dfile))
        return 0


def find_NearFacilityList(nnn):
    arcpy_print("find_NearFacilityList()")
    global NearFacilityList
    if len(NearFacilityList) > 0: return
    NearFacilityList = []
    n = nnn  # num_districts
    if n > num_districts: n = num_districts
    dis = 0.0
    for i in range(num_units):
        if i % 100 == 0: arcpy_print(".")
        fdlist = [[x, nodedik[i][x]] for x in range(num_districts)]
        fdlist.sort(key=lambda x: x[1])
        flist = [x[0] for x in fdlist[0:n]]
        NearFacilityList.append(flist[:])
    if geo_instance == 0:
        return


def find_near_customer():
    global nearCustomer
    global nearCustomers
    if location_problem >= 2 and pmp_I_eaquls_J == 1:
        nearCustomers = NearFacilityList
        nearCustomer = [x for x in range(num_districts)]
        return
    nearCustomer = [-1 for x in range(num_districts)]
    nearCustomers = [[] for x in range(num_districts)]
    dis = []
    for k in range(num_districts):
        dis = [[x, nodedij[x][k]] for x in range(num_units)]
        dis.sort(key=lambda x: x[1])
        nearCustomer[k] = dis[0][0]
        nearCustomers[k] = [x[0] for x in dis]


# 此函数没有运行，直接return,20230213
def create_facility_neighbors():
    return
    global facility_neighbors
    mindij = [[MAXNUMBER for x in range(num_districts)] for y in range(num_districts)]
    for i in range(num_districts):
        for j in range(num_districts):
            if j <= i: continue
            dlist = [nodedij[x][i] - nodedij[x][j] for x in range(num_units)]
            d = sum(x * x for x in dlist)
            mindij[i][j] = d
            mindij[j][i] = d
    facility_neighbors = [[] for x in range(num_districts)]
    for i in range(num_districts):
        dlist = [[x, mindij[i][x]] for x in range(num_districts)]
        dlist.sort(key=lambda x: x[1])
        nghrs = [x[0] for x in dlist]
        facility_neighbors[i] = nghrs[:]


def k_medoids_cflpr_sampling(num_k):
    global centersID
    global node_groups
    centers = []
    sol = [-1 for x in range(num_units)]
    distance_obj = 0.0
    while 1:
        if len(centers) == num_k: break
        k = random.randint(0, num_districts - 1)
        if k not in centers: centers.append(k)
    # for i in range(num_units):
    #    for k in NearFacilityList[i]:
    #        if k in centers:
    #            distance_obj+=nodedik[i][k]
    #            sol[i]=k
    #            break
    centers2 = []
    sol2 = [-1 for x in range(num_units)]
    distance_obj2 = 0.0
    loop = 0
    # k-means
    while 1:
        loop += 1
        distance_obj = 0.0
        for i in range(num_units):
            for k in NearFacilityList[i]:
                if k in centers:
                    sol[i] = k
                    distance_obj += nodedik[i][k]
                    break
        distance_obj2 = 0.0
        centers2 = []
        for k in centers:
            ulist = [x for x in range(num_units) if sol[x] == k]
            if len(ulist) == 0: continue
            clist = range(num_districts)
            cid = -1
            mindis = MAXNUMBER
            for i in clist:
                dsum = sum(nodedik[x][i] for x in ulist)
                if dsum < mindis:
                    mindis = dsum
                    cid = i
            centers2.append(cid)
            distance_obj2 += mindis
            for i in ulist: sol2[i] = cid
        sol = sol2[:]
        centers = list(set(centers2))
        if abs(distance_obj2 - distance_obj) / distance_obj < 0.0001:
            break
    return centers


# update region information of the current solution
def update_district_info():
    global objective_overload
    global objective
    global biobjective
    global objective_fcost
    global district_info
    global move_count
    global obj_balance
    global centersID
    global objective_supply
    global avg_dis_min
    for k in range(num_districts):
        district_info[k][0] = 0
        district_info[k][1] = 0.0
        district_info[k][2] = 0.0
        district_info[k][3] = 0.0
        district_info[k][4] = 0.0
    for k in range(num_districts):
        if centersID[k] < 0 and k in node_groups:
            arcpy_print("debug: a facility not selected but used:{0}".format(str(k)))
            centersID[k] = facilityCandidate[k]
    for k in range(num_districts):
        if centersID[k] < 0:
            continue
        ulist = [x for x in range(num_units) if node_groups[x] == k]
        if len(ulist) == 0:
            if location_problem == 3: continue
            if adaptive_number_of_facilities == 1 and k not in facility_inclusion_list:
                centersID[k] = -1
                continue
        district_info[k][0] = len(ulist)
        district_info[k][1] = sum(nodes[x][3] for x in ulist)
        district_info[k][2] = sum(nodedik[x][k] for x in ulist)
        district_info[k][3] = facilityCapacity[k]
        district_info[k][4] = max(0.0, district_info[k][1] - facilityCapacity[k])  # -district_info[k][3]
        if location_problem == 3: district_info[k][4] = 0  # pmp
        if location_problem == 2:  # pdp,edp
            bal = 0.0
            dev = pop_deviation * total_pop / max_num_facility
            if district_info[k][1] > district_info[k][3] + dev: bal = district_info[k][1] - district_info[k][3] - dev
            if district_info[k][1] < district_info[k][3] - dev: bal = district_info[k][3] - district_info[k][1] - dev
            district_info[k][4] = bal
    bal = sum(x[4] for x in district_info)
    objective = sum([x[2] for x in district_info])
    objective_overload = bal
    # if objective/total_pop<avg_dis_min:
    #    avg_dis_min=objective/total_pop
    avg_dis_min = objective / total_pop
    biobjective = objective + objective_overload * avg_dis_min * pop_dis_coeff

    objective_supply = sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >= 0)
    # biobjective=objective+objective_overload*avg_dis_min*1000000
    # biobjective=bal2*avg_dis_min*1000000
    if fixed_cost_obj == 1:
        fcost = sum(facilityCost[x] for x in range(num_districts) if centersID[x] >= 0)
        objective_fcost = fcost
        biobjective += fcost
    move_count += 1


def location_model_linear_relexation(numf, r, maxtime, mipgap):
    global node_groups
    global centersID
    global num_districts
    global district_info
    if mip_solver not in mip_solvers:
        return -9
    alpha_coeff = avg_dis_min * pop_dis_coeff
    prob = pulp.LpProblem("location", pulp.LpMinimize)
    xvariables = {}
    costs = {}
    alpha_coeff = avg_dis_min * pop_dis_coeff
    for i in range(num_units):
        for j in range(num_districts):
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpContinuous)
            if r == 0:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]
            if r == 1:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] * (random.random() + 19.5) / 20
    yvariables = {}
    for i in range(num_districts):
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpContinuous)
        costs["y_" + str(i)] = facilityCost[i]

    obj = ""
    for x in xvariables:
        obj += costs[x] * xvariables[x]
    if fixed_cost_obj == 1:
        for y in yvariables:
            if costs[y] > 0.0:
                obj += costs[y] * yvariables[y]
    prob += obj

    ##    for k in facilityCandidate:
    ##        if nodes[k][6]!=1:
    ##            continue
    ##        s=xvariables["x_" +str(k)+ "_"+ str(k)]
    ##        prob +=s == 1

    ##    for k in facilityCandidate:
    ##        if nodes[k][6]==1:
    ##            s=yvariables["y_" +str(k)]
    ##            prob +=s == 1

    # con2 1
    s = ""
    for k in range(num_districts):
        s += yvariables["y_" + str(k)]
    if adaptive_number_of_facilities == 0:
        prob += s == numf
    # else:
    #    prob +=s == numf
    # cons 2
    for i in range(num_units):
        s = ""
        for j in range(num_districts):
            s += xvariables["x_" + str(i) + "_" + str(j)]
        prob += s == 1
    # cons 3
    for k in range(num_districts):
        s = ""
        for i in range(num_units):
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
        # s-=hvariables["h_" +str(k)]
        s -= facilityCapacity[k] * yvariables["y_" + str(k)]
        # s-=facilityCapacity[k]
        prob += s <= 0
    # cons 4
    # for k in range(num_districts):
    #    s=hvariables["h_" +str(k)]-100000*yvariables["y_" +str(k)]
    #    prob+=s <= 0
    # cons 5 #can be removed
    for i in range(num_units):
        for k in range(num_districts):
            s = nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)] - facilityCapacity[k] * yvariables["y_" + str(k)]
            prob += s <= 0

    # prob.writeLP("_location.lp")
    # maxSeconds=heuristic_time_limit/multi_start_count/2
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(msg=solver_message, timeLimit=maxtime, gapRel=gap,
                                    options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message, timeLimit=maxtime)
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(msg=solver_message, options=[("MIPGap", gap), ("TimeLimit", maxtime)])
    solver.setTmpDir()
    solver.actualSolve(prob)

    if prob.status <= 0:
        return prob.status
    sol = [[x, 0.0, []] for x in range(num_districts)]
    yk = [0.0 for x in range(num_districts)]
    node_groups = [-1 for x in range(num_units)]
    for v in prob.variables():
        if (v.varValue > 0.0):
            ###noprint v,v.varValue
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                sol[i][1] = v.varValue
                yk[i] = v.varValue
                continue
            if items[0] == 'h': continue
            k = int(items[2])
            sol[k][1] += nodes[i][3] * v.varValue
            sol[k][2].append([i, nodedik[i][k] * v.varValue])
    return yk, sol


def initialize_instance():
    global num_units
    global num_districts
    global num_facilityCandidate
    global centersID
    global node_groups
    global facilityCost
    global facilityCandidate
    global facilityCapacity
    global nodedik
    global avg_pop
    global total_pop
    global avg_dis_min
    global total_supply
    global fixed_cost_obj
    global max_num_facility
    global adaptive_number_of_facilities
    # solution obj
    global district_info
    global objective_overload
    global objective
    global biobjective
    global all_solutions
    # best solution
    global best_solution
    global best_centersID
    global best_biobjective
    global best_objective
    global best_objective_overload
    # global best solution
    global best_solution_global
    global best_centersID_global
    global best_biobjective_global
    global best_objective_global
    global best_overload_global
    global potential_facilities
    global max_exclusion_list
    num_districts = len(facilityCandidate)
    # num_units=len(nodes)
    total_pop = sum(x[3] for x in nodes)
    # print total_pop,nodes[:10]
    # sum(nodes[x][3] for x in range(num_units))
    node_groups = [-1 for x in range(num_units)]
    if location_problem == 0:
        fixed_cost_obj = 0
        max_num_facility = num_districts
    if fixed_cost_obj == 0:
        facilityCost = [0 for x in range(num_districts)]
    if location_problem == 1 and max_num_facility < 1:
        max_num_facility = num_districts
        adaptive_number_of_facilities = 1
    if location_problem == 2:
        if all_units_as_candadate_locations == 1:
            facilityCandidate = [x for x in range(num_districts)]
            facilityCost = [0.0 for x in range(num_districts)]
            popa = total_pop * 1.0 / max_num_facility
            facilityCapacity = [popa for x in range(num_districts)]
        if all_units_as_candadate_locations == 0:
            facilityCost = [0.0 for x in range(num_districts)]
            popa = total_pop * 1.0 / max_num_facility
            facilityCapacity = [popa for x in range(num_districts)]
    if location_problem == 3:  # pmp
        # num_districts=num_units
        # facilityCandidate=[x for x in range(num_districts)]
        facilityCost = [0.0 for x in range(num_districts)]
        facilityCapacity = [total_pop for x in range(num_districts)]
    centersID = facilityCandidate[:]
    num_facilityCandidate = len(facilityCandidate)
    district_info = [[0, 0.0, 0.0, 0.0, 0.0] for x in range(num_districts)]
    total_supply = sum(facilityCapacity)
    objective_overload = MAXNUMBER
    obj_balance = MAXNUMBER
    objective = MAXNUMBER
    biobjective = MAXNUMBER
    all_solutions = []

    # best solution in each start
    best_solution = []  # node_groups[:]
    best_centersID = []
    best_biobjective = MAXNUMBER
    best_objective = MAXNUMBER
    best_objective_overload = MAXNUMBER

    # global best solution
    best_solution_global = []
    best_centersID_global = []
    best_biobjective_global = MAXNUMBER
    best_objective_global = MAXNUMBER
    best_overload_global = MAXNUMBER
    # if geo_instance==1:
    #    nodedik=[[nodedij[y][facilityCandidate[x]]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
    avg_dis_min = sum(nodedik[x][0] for x in range(num_units)) / total_pop
    if spatial_contiguity >= 1:
        find_near_customer()
    find_NearFacilityList(num_districts)
    if linear_relaxation == 1:
        lplocs, sol = location_model_linear_relexation(max_num_facility, 0, heuristic_time_limit, 0.0001)
        potential_facilities = [x for x in range(num_districts) if lplocs[x] > 0.0001]
        arcpy_print("Potential facilities by Linear Relax:{0}".format(potential_facilities))
    max_exclusion_list = [0.0 for x in range(num_districts)]


def lscp_mip_model_init(max_radius, cover_pecentage, time_limit, mipgap):
    global centersID
    global node_groups
    prob = pulp.LpProblem("pcp", pulp.LpMinimize)
    centers = range(num_districts)  # facilityCandidate
    sampling = 0
    if total_supply > 10 * total_pop:
        sampling = 1
        min_nf = total_pop * num_districts / total_supply
        centers = k_medoids_cflpr_sampling(min_nf * 10)
    else:
        random.shuffle(centers)
        centers = centers[:num_districts * 9 / 10]
    if total_supply > 15000 * total_pop:
        centers = []
        ilist = []
        supply = 0
        try_count = 0
        while supply < 15 * total_pop:
            if try_count > num_districts: break
            try_count += 1
            k = random.randint(0, num_districts - 1)
            if len(ilist) > 0:
                mind = min(nodedij[x][k] for x in ilist)
                if mind < max_radius * 0.5: continue
            if k not in centers:
                centers.append(k)
                ilist.append(nearCustomer[k])
                supply += facilityCapacity[k]
                try_count = 0
            # print [try_count,len(centers),supply],
    centers = list(set(centers + facility_inclusion_list))
    ulist = range(num_units)
    xvariables = {}
    costs = {}
    yvariables = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
        costs["y_" + str(i)] = facilityCost[i]
    zvariables = {}
    for i in ulist:
        zvariables["z_" + str(i)] = pulp.LpVariable("z_" + str(i), 0, 1, pulp.LpInteger)

    obj = ""
    for x in yvariables:
        obj += costs[x] * yvariables[x]
    prob += obj

    min_nf = total_pop * num_districts / total_supply
    # con 1
    # s=""
    # for k in centers:
    #    s+=yvariables["y_" +str(k)]
    # prob +=s >= min_nf
    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    s = ""
    for k in centers:
        s += facilityCapacity[k] * yvariables["y_" + str(k)]
    prob += s >= total_pop

    # cons 2
    for i in ulist:
        s = ""
        for j in centers:
            if nodedij[i][j] > max_radius: continue
            s += yvariables["y_" + str(j)]
        prob += s - zvariables["z_" + str(i)] >= 0

    #    for i in ulist:
    #        for j in centers:
    #            if nodedij[i][j]>max_radius: continue
    #            s=yvariables["y_" + str(j)]+ zvariables["z_" +str(i)]
    #            prob +=s <= 1

    s = ""
    for i in ulist:
        r = 1
        if sampling == 0:
            r = (49.5 + random.random()) / 50
        s += nodes[i][3] * r * zvariables["z_" + str(i)]
    prob += s >= total_pop * cover_pecentage / 100
    # maxuc=total_pop-total_pop*cover_pecentage/100
    # prob += s<=maxuc
    prob.writeLP("_lscp.lp")
    # initvalues=pmp_mst(dlist,ulist)
    # for x,v in initvalues:
    #    if x.find("x")==0:  xvariables[x].setInitialValue(v)
    #    if x.find("y")==0:  yvariables[x].setInitialValue(v)
    # warmStart=True,
    # solver_message=1
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap), 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)

    if prob.status <= 0:
        arcpy_print("model unsolved...6")
        return 0
    centersID = [-1 for x in range(num_districts)]
    if len(node_groups) < 1: node_groups = [-1 for x in range(num_units)]
    for v in prob.variables():
        if (v.varValue >= 0.90):
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
    for i in range(num_units):
        for k in NearFacilityList[i]:
            if centersID[k] >= 0:
                node_groups[i] = k
                break
    update_district_info()
    return 1


# TESTING
def clscp_mip_model_init(max_radius, cover_pecentage, time_limit, mipgap):
    global centersID
    global node_groups
    global district_info
    prob = pulp.LpProblem("clscp", pulp.LpMinimize)
    centers = range(num_districts)  # facilityCandidate
    sampling = 0
    if total_supply > 10 * total_pop:
        sampling = 1
        min_nf = total_pop * num_districts / total_supply
        centers = k_medoids_cflpr_sampling(min_nf * 10)
        centers = list(set(centers + facility_inclusion_list))

    covered_units = [[] for x in range(num_districts)]
    covered_cost = [facilityCost[x] for x in range(num_districts)]
    for k in range(num_districts):
        covered = []
        if k not in centers: continue
        supply = facilityCapacity[k] * 1.15
        if sampling == 0:
            supply = facilityCapacity[k] * (1.15 + random.random() / 20)  # pie*r*r / 2.6*r*r = pie/2.6=
        cost = 0.0
        for i in nearCustomers[k]:
            if nodedij[i][k] > max_radius: break
            if supply < nodes[i][3]: break
            supply -= nodes[i][3]
            covered.append(i)
            cost += nodedik[i][k]
        covered_units[k] = covered[:]
        covered_cost[k] += cost
    avg_covered_cost = sum(covered_cost) / num_districts
    ulist = range(num_units)
    yvariables = {}
    cost = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
        cost["y_" + str(i)] = facilityCost[i]
    zvariables = {}
    for i in ulist:
        zvariables["z_" + str(i)] = pulp.LpVariable("z_" + str(i), 0, 1, pulp.LpInteger)
    obj = ""
    # for x in yvariables:
    #    obj += yvariables[x]
    for k in centers:
        obj += covered_cost[k] * yvariables["y_" + str(k)]
        # obj += (100000000 + abs(covered_cost[k]-avg_covered_cost))*yvariables["y_" +str(k)]
    prob += obj
    s = ""
    for k in centers:
        s += facilityCapacity[k] * yvariables["y_" + str(k)]
    prob += s >= total_pop

    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    if adaptive_number_of_facilities == 0:
        s = ""
        for k in centers:
            s += yvariables["y_" + str(k)]
        prob += s == max_num_facility
    for i in ulist:
        s = ""
        for j in centers:
            if i in covered_units[j]:
                s += yvariables["y_" + str(j)]
        s -= zvariables["z_" + str(i)]
        prob += s >= 0

    if cover_pecentage >= 99:
        for i in ulist:
            prob += zvariables["z_" + str(i)] == 1
    else:
        s = ""
        for i in ulist:
            s += nodes[i][3] * zvariables["z_" + str(i)]
        prob += s >= total_pop * cover_pecentage / 100.0
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap), 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved...")
        return 0
    centersID = [-1 for x in range(num_districts)]
    node_groups = [-1 for x in range(num_units)]
    fselected = []
    for v in prob.variables():
        if (v.varValue >= 0.90):
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
                fselected.append(i)
    for k in fselected:
        for i in covered_units[k]:
            if node_groups[i] == -1: node_groups[i] = k
            if node_groups[i] >= 0:
                k2 = node_groups[i]
                if nodedij[i][k] < nodedij[i][k2]: node_groups[i] = k
    update_district_info()
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            if facilityCapacity[k] - district_info[k][1] >= nodes[i][3]:
                node_groups[i] = k
                district_info[k][1] += nodes[i][3]
                break
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            node_groups[i] = k
            break
    update_district_info()
    # for x in district_info:
    #    if x[0]>0: print x
    return 1


def clscp_mip_model_init2(maxr2, maxr, cover_pecentage, time_limit, mipgap):
    global centersID
    global node_groups
    global district_info
    prob = pulp.LpProblem("_clscp", pulp.LpMinimize)
    centers = range(num_districts)  # facilityCandidate
    sampling = 0
    if total_supply > 10 * total_pop:
        sampling = 1
        min_nf = total_pop * num_districts / total_supply
        centers = k_medoids_cflpr_sampling(min_nf * 10)
        centers = list(set(centers + facility_inclusion_list))
    covered_units = [[] for x in range(num_districts)]
    covered_cost = [facilityCost[x] for x in range(num_districts)]
    for k in range(num_districts):
        covered = []
        if k not in centers: continue
        supply = facilityCapacity[k] * 1.15  # pie*r*r / 2.6*r*r = pie/2.6=
        if sampling == 0:
            supply = facilityCapacity[k] * (1.15 + random.random() / 20)  # pie*r*r / 2.6*r*r = pie/2.6=
        cost = 0.0
        for i in nearCustomers[k]:
            if nodedij[i][k] > maxr2: break
            if supply < nodes[i][3]: break
            supply -= nodes[i][3]
            covered.append(i)
            cost += nodedik[i][k]
        covered_units[k] = covered[:]
        covered_cost[k] += cost
    avg_covered_cost = sum(covered_cost) / num_districts
    ulist = range(num_units)
    yvariables = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
    zvariables = {}
    for i in ulist:
        zvariables["z_" + str(i)] = pulp.LpVariable("z_" + str(i), 0, 1, pulp.LpInteger)
    obj = ""
    for k in centers:
        obj += covered_cost[k] * yvariables["y_" + str(k)]
    prob += obj
    s = ""
    for k in centers:
        s += facilityCapacity[k] * yvariables["y_" + str(k)]
    prob += s >= total_pop

    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    if adaptive_number_of_facilities == 0:
        s = ""
        for k in centers:
            s += yvariables["y_" + str(k)]
        prob += s == max_num_facility

    for i in ulist:
        s = ""
        for j in centers:
            if nodedij[i][j] > maxr: continue
            if i in covered_units[j]:
                s += yvariables["y_" + str(j)]
        s -= zvariables["z_" + str(i)]
        prob += s >= 0

    for i in ulist:
        s = ""
        for j in centers:
            if i in covered_units[j]:
                s += yvariables["y_" + str(j)]
        prob += s >= 1

    if cover_pecentage >= 99:
        for i in ulist:
            prob += zvariables["z_" + str(i)] == 1
    else:
        s = ""
        for i in ulist:
            s += nodes[i][3] * zvariables["z_" + str(i)]
        prob += s >= total_pop * cover_pecentage / 100.0
    prob.writeLP("_sclp_init3.lp")
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap), 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved...8")
        return 0
    centersID = [-1 for x in range(num_districts)]
    node_groups = [-1 for x in range(num_units)]
    fselected = []
    for v in prob.variables():
        if (v.varValue >= 0.90):
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
                fselected.append(i)
    for k in fselected:
        for i in covered_units[k]:
            if node_groups[i] == -1: node_groups[i] = k
            if node_groups[i] >= 0:
                k2 = node_groups[i]
                if nodedij[i][k] < nodedij[i][k2]: node_groups[i] = k
    update_district_info()
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            if facilityCapacity[k] - district_info[k][1] >= nodes[i][3]:
                node_groups[i] = k
                district_info[k][1] += nodes[i][3]
                break
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            node_groups[i] = k
            break
    update_district_info()
    return 1


def location_drop_cflpr(max_radius2, max_radius, cover_pecentage):
    global centersID
    global node_groups
    clist = [x for x in range(num_districts) if centersID[x] >= 0 and x not in facility_inclusion_list]
    if clist == []: return 0
    dlist = []
    random.shuffle(clist)
    for k in clist:
        ids = centersID[:]
        ids[k] = -1
        ulist = [[x, nodes[x][3]] for x in range(num_units) if node_groups[x] == k]
        ulist.sort(key=lambda x: -x[1])
        savings = district_info[k][2]
        savings += facilityCost[k]
        caplist = [facilityCapacity[x] - district_info[x][1] for x in range(num_districts)]
        caplist[k] = 0
        assigned = 0
        for x, y in ulist:
            assigned = 0
            for r in NearFacilityList[x]:
                if centersID[r] < 0: continue
                if r == k: continue
                if y <= caplist[r]:
                    savings -= nodedik[x][r]
                    caplist[r] -= y
                    assigned = 1
                    break
            if assigned == 0: break
        if assigned == 1: dlist.append([k, savings])
    if len(dlist) == 0: return -1
    dlist.sort(key=lambda x: -x[1])
    update_district_info()
    f_del = 0
    tabu = []
    status = 0
    while 1:
        if len(dlist) < 1: break
        temp = [centersID[:], node_groups[:]]
        r = random.random()
        idx = int(r * 0.999 * min(3, len(dlist)))
        k = dlist[idx][0]
        del dlist[idx]
        if k in tabu: continue
        centersID[k] = -1
        ulist = [[x, nodes[x][3]] for x in range(num_units) if node_groups[x] == k]
        ulist.sort(key=lambda x: -x[1])
        caplist = [district_info[x][3] - district_info[x][1] for x in range(num_districts)]
        caplist[k] = 0
        assigned = 1
        for x, y in ulist:
            assigned = 0
            for r in NearFacilityList[x]:
                if centersID[r] < 0: continue
                if y <= caplist[r]:
                    caplist[r] -= y
                    node_groups[x] = r
                    assigned = 1
                    if r not in tabu: tabu.append(r)
                    break
            if assigned == 0: break
        if assigned == 0:
            centersID = temp[0][:]
            node_groups = temp[1][:]
            update_cflpr_district_info(max_radius2, max_radius, cover_pecentage)
            return status
        update_cflpr_district_info(max_radius2, max_radius, cover_pecentage)
        # print objective,objective_fcost,objective_overload
        status = 1
        f_del += 1
        if f_del >= len(clist) / 20 or f_del >= 10: break
        supply = sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >= 0)
        if supply <= total_pop * 3: break
    return status


def drop_method_cflpr(max_radius2, max_radius, cover_pecentage):
    global node_groups
    global centersID
    global all_solutions
    sol = []
    node_groups = [NearFacilityList[x][0] for x in range(num_units)]
    centersID = facilityCandidate[:]
    # for x in range(num_districts):
    #    if x not in node_groups: centersID[x]=-1
    if total_supply > 10 * total_pop:
        centersID = [-1 for x in range(num_districts)]
        sampling = 1
        min_nf = total_pop * num_districts / total_supply
        centers = k_medoids_cflpr_sampling(min_nf * 10)
        centers = list(set(centers + facility_inclusion_list))
        for k in centers: centersID[k] = facilityCandidate[k]

    if total_supply > total_pop * 1000:
        supply = 0
        centersID = [-1 for x in range(num_districts)]
        try_count = 0
        while supply < total_pop * 10:
            k = random.randint(0, num_districts - 1)
            if try_count >= num_districts / 2: break
            if centersID[k] >= 0: continue
            if supply > 0:
                u = nearCustomers[k][0]
                min_dis = min(nodedij[u][x] for x in range(num_districts) if centersID[x] >= 0)
                if min_dis < max_radius * 0.6:
                    try_count += 1
                    continue
            supply += facilityCapacity[k]
            centersID[k] = facilityCandidate[k]
            try_count = 0
    for i in range(num_units):
        for k in NearFacilityList[i]:
            if centersID[k] == -1: continue
            node_groups[i] = k
            break
    update_cflpr_district_info(max_radius, max_radius, cover_pecentage)
    while 1:
        sol = [centersID[:], node_groups[:]]
        sta = location_drop_cflpr(max_radius2, max_radius, cover_pecentage)  # too slow for large instances, sampling ?
        update_cflpr_district_info(max_radius2, max_radius, cover_pecentage)
        # update_district_info()
        if sta <= 0: break
        coverdemand = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= max_radius: coverdemand += nodes[i][3]
        cp = coverdemand * 100.0 / total_pop
        # if adaptive_number_of_facilities==1 and cp<cover_pecentage: break
        # print biobjective, objective_overload,cp
        if cp < cover_pecentage:
            # centersID=sol[0][:]
            # node_groups=sol[1][:]
            # update_cflpr_district_info(max_radius,cover_pecentage)
            break
        # print biobjective, objective,objective_fcost,objective_overload, cp
        sol = [biobjective, centersID[:], node_groups[:]]
        nf = sum(1 for x in centersID if x >= 0)
        if adaptive_number_of_facilities == 0 and nf <= max_num_facility:
            sol = [biobjective, centersID[:], node_groups[:], objective, objective_fcost, objective_overload, 0]
            break
    # if len(sol)>0:
    #    node_groups=sol[2][:]
    #    centersID=sol[1][:]
    #    update_cflpr_district_info(max_radius,cover_pecentage)
    nf = sum(1 for x in centersID if x >= 0)
    if adaptive_number_of_facilities == 0 and nf > max_num_facility:
        droplist = []
        dlist = [x for x in range(num_districts) if centersID[x] >= 0]
        while len(dlist) > max_num_facility:
            random.shuffle(dlist)
            k = dlist[0]
            if k in facility_inclusion_list: continue
            dlist.remove(k)
            droplist.append(k)
            # print [len(dlist),len(droplist)],
        # print droplist
        for x in droplist: centersID[x] = -1
        ulist = [x for x in range(num_units) if node_groups[x] in droplist]
        for i in ulist:
            for k in NearFacilityList[i]:
                if centersID[k] < 0: continue
                node_groups[i] = k
                break
        # update_cflpr_district_info(max_radius,cover_pecentage)
        update_district_info()
        coverdemand = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= max_radius: coverdemand += nodes[i][3]
        cp = coverdemand * 100.0 / total_pop
    return 1


def update_zero_demand():
    global node_groups
    for i in range(num_units):
        if nodes[i][3] > 0: continue
        for k in NearFacilityList[i]:
            if centersID[k] >= 0:
                node_groups[i] = k
                break


def update_cflpr_district_info(max_radius2, max_radius, cover_pecentage):
    global biobjective
    update_district_info()
    penalty_demands = objective_overload
    covered = 0
    covered2 = 0
    for i in range(num_units):
        k = node_groups[i]
        if nodedij[i][k] <= max_radius: covered += nodes[i][3]
        if nodedij[i][k] > max_radius2: covered2 += nodes[i][3]
    penalty_demands += max(0, total_pop * cover_pecentage / 100 - covered)
    penalty_demands += covered2
    # penalty=max(facilityCost)
    # penalty=10*sum(facilityCost)/sum(facilityCapacity)
    penalty = max(facilityCost) / (sum(facilityCapacity) / num_districts / 100)
    # if soft_constraint==1: penalty=max(facilityCost)
    # penalty=current_penalty(max_radius2,max_radius,cover_pecentage)
    # penalty=max(facilityCost)*num_districts*10/sum(facilityCapacity)
    # print [biobjective,objective_overload,max(0, total_pop*cover_pecentage/100.0-covered),penalty_demands,penalty]
    biobjective = objective_fcost + objective + penalty * penalty_demands


cflpr_search_time = [0.0, 0.0, 0.0, 0.0, 0.0]
cflpr_search_improves = [0, 0, 0, 0, 0]


def assign_CFLPr1(maxr2, maxr, mincp):  # improve coverage or distance
    global node_groups
    global cflpr_search_time
    t = time.time()
    ulist = []
    for i in range(num_units):
        if nodes[i][3] == 0: continue
        k = node_groups[i]
        if nodedij[i][k] > maxr:
            ulist.append(i)
    if ulist == []: return
    random.shuffle(ulist)
    cover = 0
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            if nodedij[i][k] >= maxr: break
            if k == node_groups[i]: break
            if nodes[i][3] <= facilityCapacity[k] - district_info[k][1]:
                node_groups[i] = k
                update_cflpr_district_info(maxr2, maxr, mincp)
                cover += nodes[i][3]
                cflpr_search_improves[0] += 1
                break
    # print "cover more:", cover,
    cflpr_search_time[0] += time.time() - t


def assign_CFLPr2(maxr2, maxr, mincp):  # min overload
    global node_groups
    global cflpr_search_time
    if objective_overload <= 0: return
    t = time.time()
    ulist = []
    overload = objective_overload
    reduced = 0
    for k in range(num_districts):
        if centersID[k] < 0: continue
        if district_info[k][4] <= 0.1: continue
        klist = [[x, nodedij[x][k]] for x in range(num_units) if node_groups[x] == k]
        klist.sort(key=lambda x: -x[1])
        ulist += [x[0] for x in klist[:len(klist) / 5]]
    if len(ulist) >= 0:
        random.shuffle(ulist)
        for i in ulist:
            k = node_groups[i]
            if district_info[k][4] <= 0: continue
            for k in NearFacilityList[i]:
                if centersID[k] < 0: continue
                if nodedij[i][k] > maxr: break
                if nodes[i][3] <= facilityCapacity[k] - district_info[k][1]:
                    node_groups[i] = k
                    update_cflpr_district_info(maxr2, maxr, mincp)
                    reduced += nodes[i][3]
                    cflpr_search_improves[1] += 1
                    break
    # print "ovld less:",overload-objective_overload,
    cflpr_search_time[1] += time.time() - t


def assign_CFLPr3(maxr2, maxr, mincp):  # min distance
    global node_groups
    global cflpr_search_time
    t = time.time()
    ulist = []
    for i in range(num_units):
        k = node_groups[i]
        if nodes[i][3] == 0: continue
        if nodedij[i][k] > maxr:  # district_info[k][2]/district_info[k][1]:
            ulist.append(i)
    if ulist == []: return
    random.shuffle(ulist)
    dis_total = 0.0
    for i in ulist:
        k = node_groups[i]
        dis = nodedij[i][k]
        for k in NearFacilityList[i]:
            if centersID[k] < 0: continue
            if nodedij[i][k] >= dis: break
            if k == node_groups[i]: break
            if nodes[i][3] <= facilityCapacity[k] - district_info[k][1]:
                node_groups[i] = k
                update_cflpr_district_info(maxr2, maxr, mincp)
                dis_total += (dis - nodedij[i][k]) * nodes[i][3]
                cflpr_search_improves[2] += 1
                break
    # print "dist less:", dis_total,
    cflpr_search_time[2] += time.time() - t


# record a region in current solution 20230209调用
def update_region_pool(rid):
    global pool_index
    global time_spp
    global region_pool
    t = time.time()
    if is_spp_modeling <= 0: return
    if centersID[rid] < 0: return
    # if spatial_contiguity==1 and check_continuality_feasibility(node_groups,rid)<1:
    #    return
    ulist = [x for x in range(num_units) if node_groups[x] == rid]
    if ulist == []:
        # print "empty area:",rid,node_groups
        return
    cost1 = district_info[rid][2]
    cost2 = sum(nodedik[x][rid] for x in ulist)
    if abs(cost1 - cost2) > 0.001: arcpy_print("rid{0},cost1{1},cost2{2}".format(rid, cost1, cost2))
    obj = district_info[rid][2] + district_info[rid][4] * pop_dis_coeff
    idx = int(obj * 100000)
    idx += sum(x * x for x in ulist)
    if idx not in pool_index[rid]:
        pool_index[rid].append(idx)
        region_pool.append([ulist, district_info[rid][2], district_info[rid][1], district_info[rid][4], rid])
    time_spp += time.time() - t
    return


# record all regions in current solution
def update_region_pool_all():
    if is_spp_modeling <= 0:
        return
    for rid in range(num_districts):
        if centersID[rid] < 0: continue
        update_region_pool(rid)


# update the best and the global best solution
# if the current solution is better than the best
def update_best_solution():
    global best_solution
    global best_centersID
    global best_biobjective
    global best_objective
    global best_objective_fcost
    global best_overload
    global best_objective_overload
    global best_centersID_global
    global best_solution_global
    global best_biobjective_global
    global best_objective_global
    global best_objective_fcost_global
    global best_overload_global
    global improved_loop
    global improved
    global avg_dis_min
    improve = 0
    if location_problem == 1 and adaptive_number_of_facilities == 0:
        nf = sum(1 for x in centersID if x >= 0)
        if nf != max_num_facility: return 0
    # if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
    #    ##noprint "check_solution_continuality_feasibility!!!"
    #    return improve
    biobj = biobjective
    biobj_best = best_biobjective
    if biobj <= biobj_best:
        best_biobjective = biobj
        best_objective = objective
        best_objective_fcost = objective_fcost
        best_objective_overload = objective_overload
        best_solution = node_groups[:]
        best_centersID = centersID[:]
        improved_loop = mainloop
        improve = 1
        improved += 1
    if biobj < best_biobjective_global:
        best_biobjective_global = biobj
        best_centersID_global = centersID[:]
        best_overload_global = objective_overload
        best_solution_global = node_groups[:]
        best_objective_global = objective
        best_objective_fcost_global = objective_fcost
        avg_dis_min = biobj / total_pop
    return improve


def select_region_adaptive(seed):
    nf = sum(1 for x in range(num_districts) if centersID[x] >= 0)
    units = num_units / nf
    n = -1
    if units >= 50:
        if nf <= 10: n = random.randint(nf / 2 + 1, nf)
        if nf >= 11 and nf <= 20: n = random.randint(8, 11)
        if nf >= 21: n = random.randint(10, 13)
    if units >= 25 and units <= 49:
        if nf <= 10: n = random.randint(nf / 2 + 1, nf)
        if nf >= 11 and nf <= 20: n = random.randint(9, 12)
        if nf >= 21: n = random.randint(11, 14)
    if units <= 20:
        if nf <= 10: n = random.randint(nf / 2 + 1, nf)
        if nf >= 11 and nf <= 20: n = random.randint(10, 13)
        if nf >= 21: n = random.randint(12, 15)
    n += len(facility_inclusion_list) * n / nf
    if n > nf: n = nf
    u = seed
    if u < 0 or u >= num_units: u = random.randint(0, num_units - 1)
    r = node_groups[u]
    clist = []
    for k in NearFacilityList[u]:
        if centersID[k] < 0: continue
        clist.append(k)
        if len(clist) == n: break
    return clist


def current_penalty(maxr2, maxr1, cp):
    # return 10*sum(facilityCost)/sum(facilityCapacity)
    return 100 * max(facilityCost) * num_districts / sum(facilityCapacity)


def sscflpr_sub_assign_model(max_radius2, max_radius, cover_pecentage, time_limit, mipgap):
    # may be more facility needed, due to the covering constraint
    global centersID
    global node_groups
    rand = 0
    if random.random() > 0.5: rand = 0
    u = random.randint(0, num_units - 1)
    if random.random() > 0.5:
        ulist = []
        if objective_overload > 0:
            rlist = [x for x in range(num_districts) if centersID[x] >= 0 and district_info[x][4] > 0]
            ulist = [x for x in range(num_units) if node_groups[x] in rlist]
        ulist += [x for x in range(num_units) if nodedij[x][node_groups[x]] > max_radius2 and nodes[x][3] > 0]
        if len(ulist) > 0:
            random.shuffle(ulist)
            u = ulist[0]
    '''centers=[node_groups[u]] #x for x in range(num_districts) if centersID[x]>=0 and x not in dlist and facilityCapacity[x] > district_info[x][1]]
    nf=sum(1 for x in centersID if x>=0)
    nnn=10
    if nf<=11: nnn=random.randint((nf_1)/2,nf)
    if nf>11 and nf<21: nnn=random.randint(8,11)
    if nf>=21: nnn=random.randint(10,14)
    for k in NearFacilityList[u]:
        if centersID[k]<0: continue
        if k not in centers: centers.append(k)
        if len(centers)>=nnn:
            break'''
    centers = select_region_adaptive(u)
    # centers=select_region_verylarge(u)
    existing_facilities = [x for x in range(num_districts) if
                           centersID[x] >= 0 and x not in centers and facilityCapacity[x] - district_info[x][1] > 0]
    ulist = [x for x in range(num_units) if nodes[x][3] > 0 and node_groups[x] in centers]
    # print [len(centers),len(existing_facilities),len(ulist)],
    old_overload = objective_overload
    prob = pulp.LpProblem("gap", pulp.LpMinimize)
    xvariables = {}
    costs = {}
    penalty = current_penalty(max_radius2, max_radius, cover_pecentage)
    # penalty=10*max_radius2
    for i in ulist:
        for j in centers:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpBinary)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]  # *nodedij[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
            if rand == 1: costs["x_" + str(i) + "_" + str(j)] *= (19.5 + random.random()) / 20
        for j in existing_facilities:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpBinary)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]  # *nodedij[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
            if rand == 1: costs["x_" + str(i) + "_" + str(j)] *= (19.5 + random.random()) / 20
    zvariable = pulp.LpVariable("z", 0, None, pulp.LpInteger)
    zvariables = {}
    for j in centers:
        zvariables["z_" + str(j)] = pulp.LpVariable("z_" + str(j), 0, None, pulp.LpInteger)
    obj = ""
    for i in ulist:
        for j in centers:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in existing_facilities:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
    for j in centers:
        obj += penalty * zvariables["z_" + str(j)]
    obj += penalty * zvariable
    prob += obj

    for i in ulist:
        s = ""
        for j in centers:
            s += xvariables["x_" + str(i) + "_" + str(j)]
        for j in existing_facilities:
            s += xvariables["x_" + str(i) + "_" + str(j)]
        prob += s == 1

    for k in centers:
        s = ""
        for i in ulist:
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
        s -= zvariables["z_" + str(k)]
        prob += s <= facilityCapacity[k]
    for k in existing_facilities:
        s = ""
        for i in ulist:
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
        prob += s <= facilityCapacity[k] - district_info[k][1]

    '''s=""
    for j in centers:
        s+=zvariables["z_" + str(j)]
    prob+= s<=sum(district_info[k][4] for k in centers)'''

    total_cover1 = 0
    total_cover2 = 0
    for i in range(num_units):
        if nodedij[i][node_groups[i]] > max_radius: continue
        if i in ulist:
            total_cover1 += nodes[i][3]
        else:
            total_cover2 += nodes[i][3]
    s = ""
    for i in ulist:
        for j in centers:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in existing_facilities:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
    s += zvariable
    min_covered = total_pop * cover_pecentage / 100 - total_cover2
    prob += s >= min_covered

    initvalues = loc_sub_mst(centers, ulist)
    for x, v in initvalues:
        if x.find("x") == 0:  xvariables[x].setInitialValue(v)
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap),
                                                        'set mip tolerances absmipgap 100', 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("MIPGapAbs", gap * objective),
                                               ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved... or infeasible, msg={0}".format(prob.status))
        prob.writeLP("_sscflpr_sub_assign.lp")
        return []
    nf = len(centers)
    nlist = []
    obj1 = 0.0
    for x in ulist: obj1 += nodedik[x][node_groups[x]]
    for x in ulist: node_groups[x] = -1
    for v in prob.variables():
        if (v.varValue >= 0.9):
            items = v.name.split('_')
            if items[0] == 'x':
                i = int(items[1])
                node_groups[i] = int(items[2])
    obj2 = 0.0
    for x in ulist: obj2 += nodedik[x][node_groups[x]]
    s = [len(centers), len(centers), nf, int(obj1), int(obj2)]
    return s


def get_cand_cflpr_locations(dlist, ulist, r, maxr):
    clist = [NearFacilityList[x][0] for x in ulist]
    clist = [x for x in clist if centersID[x] < 0]
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0:
                if k not in clist: clist.append(k)
                break
    clist = list(set(clist))

    cloclist = []
    mewclist = []
    n = int(len(dlist) * r)
    '''maxlist=[]
    maxd=0
    for i in ulist:
        k=node_groups[i]
        if nodedij[i][k]>maxr:
            maxlist.append(i)
            maxd+=nodes[i][3]
    mewclist=[]
    if maxd>0 and random.random()>0.66 and maxd<sum(facilityCapacity[x] for x in dlist)/len(dlist)/100:
        for k in clist:
            d=min(nodedij[i][k] for i in maxlist)
            if d<maxr: mewclist.append(k)'''
    while len(cloclist) < 10:
        random.shuffle(clist)
        m = max(n - len(mewclist), n / 2)
        rlist = mewclist + clist[:n]
        rlist = list(set(rlist))
        cloclist.append(rlist)
    return cloclist


def loc_sub_mst(dlist, ulist):
    vars = []
    for i in ulist:
        k = node_groups[i]
        if k < 0: continue
        v = 'x_' + str(i) + '_' + str(k)
        vars.append([v, 1])
    for i in dlist:
        if centersID[i] < 0: continue
        v = 'y_' + str(i)
        vars.append([v, 1])
    return vars


def cflpr_sub_model(max_radius2, max_radius, cover_pecentage, time_limit, mipgap):
    global centersID
    global node_groups
    nf = sum(1 for x in range(num_districts) if centersID[x] >= 0)
    u = -1
    if random.random() > 0.33:
        ulist = []
        if objective_overload > 0:
            rlist = [x for x in range(num_districts) if centersID[x] >= 0 and district_info[x][4] > 0]
            ulist = [x for x in range(num_units) if node_groups[x] in rlist]
        ulist += [x for x in range(num_units) if nodedij[x][node_groups[x]] > max_radius2 and nodes[x][3] > 0]
        if len(ulist) > 0:
            random.shuffle(ulist)
            u = ulist[0]

    # dlist=select_region(u)
    dlist = select_region_adaptive(u)
    ulist = [x for x in range(num_units) if nodes[x][3] > 0 and node_groups[x] in dlist]
    cloclist = get_cand_cflpr_locations(dlist, ulist, 1.0, max_radius2)

    overl = sum(district_info[x][4] for x in dlist)
    # print overl,
    centers = []
    for clist in cloclist:
        tblist = list(set(clist + dlist))
        tblist.sort()
        centers = tblist
        break
    arcpy_print([len(dlist), len(centers), len(ulist)])
    exist_facility = [x for x in range(num_districts) if centersID[x] >= 0 and x not in centers and facilityCapacity[x] - district_info[x][1] > 0]
    # exist_facility=[]
    prob = pulp.LpProblem("cflpr", pulp.LpMinimize)
    xvariables = {}
    costs = {}
    penalty = current_penalty(max_radius2, max_radius, cover_pecentage)
    '''penalty=10000000000*num_districts/total_supply
    soft_demand=objective_overload
    soft_demand+= sum([nodes[x][3] for x in range(num_units) if nodedij[x][node_groups[x]] >max_radius2])
    if soft_demand>0:
        while soft_demand*penalty<10000000000:
            penalty*=10 '''
    for i in ulist:
        for j in centers:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpContinuous)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]  # *nodedij[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
        for j in exist_facility:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpContinuous)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
    yvariables = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
        costs["y_" + str(i)] = facilityCost[i]
    zvariable = pulp.LpVariable("z", 0, None, pulp.LpContinuous)
    z2variables = {}
    for i in centers:
        z2variables["z2_" + str(i)] = pulp.LpVariable("z2_" + str(i), 0, None, pulp.LpInteger)
    obj = ""
    for x in yvariables:
        obj += costs[x] * yvariables[x]
    for i in ulist:
        for j in centers:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
    # if cover_pecentage>=99: penalty*=10
    for x in z2variables:
        obj += penalty * 2 * z2variables[x]
    obj += penalty * zvariable  # 100*100000000*zvariable #*sum(facilityCost)/num_districts*zvariable
    prob += obj

    for i in ulist:
        s = ""
        for j in centers:
            s += xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            v = "x_" + str(i) + "_" + str(j)
            if v in xvariables: s += xvariables[v]
        prob += s == 1

    for k in centers:
        s = ""
        for i in ulist:
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
        s -= facilityCapacity[k] * yvariables["y_" + str(k)]
        s -= z2variables["z2_" + str(k)]
        prob += s <= 0

    for k in centers:
        s = z2variables["z2_" + str(k)] - facilityCapacity[k] * yvariables["y_" + str(k)]
        prob += s <= 0

    for k in exist_facility:
        s = ""
        for i in ulist:
            v = "x_" + str(i) + "_" + str(k)
            if v in xvariables: s += nodes[i][3] * xvariables[v]
        prob += s <= facilityCapacity[k] - district_info[k][1]

    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    total_cover1 = 0
    total_cover2 = 0
    for i in range(num_units):
        if nodedij[i][node_groups[i]] > max_radius: continue
        if i in ulist:
            total_cover1 += nodes[i][3]
        else:
            total_cover2 += nodes[i][3]
    min_covered = total_pop * cover_pecentage / 100 - total_cover2
    s = ""
    for i in ulist:
        for j in centers:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
    s += zvariable
    prob += s >= min_covered

    s = ""
    for x in yvariables: s += yvariables[x]
    numf = sum(1 for x in centersID if x >= 0)
    if adaptive_number_of_facilities == 0:
        if numf == max_num_facility:
            prob += s == len(dlist)
    else:
        soft_demand = objective_overload
        soft_demand += sum([nodes[x][3] for x in range(num_units) if nodedij[x][node_groups[x]] > max_radius2])
        covered = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] < max_radius:
                covered += nodes[i][3]
        soft_demand += max(0, total_pop * cover_pecentage / 100 - covered)
        if soft_demand > total_pop / nf / 100:
            prob += s >= len(dlist)
            prob += s <= len(dlist) + 2
        if soft_demand <= total_pop / nf: prob += s <= len(dlist) + 1
        if soft_demand > total_pop / nf: prob += s <= len(dlist) + 2

    '''else:
        ngap=max(1,nf*5/100)
        prob += s>= len(dlist)-ngap
        prob += s<= len(dlist)+ngap'''
    prob.writeLP("_CFLP.lp")
    initvalues = loc_sub_mst(dlist, ulist)
    for x, v in initvalues:
        if x.find("x") == 0:  xvariables[x].setInitialValue(v)
        if x.find("y") == 0:  yvariables[x].setInitialValue(v)
    # warmStart=True,
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap),
                                                        'set mip tolerances absmipgap 100', 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("MIPGapAbs", gap * objective),
                                               ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved... or infeasible, msg={0}".format(prob.status))
        prob.writeLP("_sscflpr_sub_model.lp")
        return []
    nf = len(dlist)
    nlist = []
    xij = [0.0 for x in range(num_units)]
    obj1 = 0.0
    for x in ulist: obj1 += nodedik[x][node_groups[x]]
    for x in dlist: centersID[x] = -1
    for x in ulist: node_groups[x] = -1
    for v in prob.variables():
        if (v.varValue >= 0.000001):
            if v.name == "z": continue
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
                nlist.append(i)
                nf -= 1
            if items[0] == 'x':
                if v.varValue > xij[i]:
                    xij[i] = v.varValue
                    node_groups[i] = int(items[2])
    return 1


def select_region(seed):
    nf = sum(1 for x in range(num_districts) if centersID[x] >= 0)
    n = 100 * nf / num_units  # areas with 100 units
    if nf <= 5: n = nf
    # if nf>=7: n=random.randint(nf/2+1,nf)
    if nf >= 6 and nf <= 11: n = random.randint(nf / 2 + 1, 9)
    if nf >= 12 and nf <= 16:
        n = random.randint(7, 10)
    if nf >= 17:
        n = random.randint(7, 10)
    if n * num_units / nf < 80:
        n = min(10, 80 * nf / num_units)
    if location_problem == 3: n = min(128, num_districts / 10)
    # clist=[]
    # u=random.randint(0,num_units-1)
    # if r>=0:
    #    u=nearCustomer[r]
    #    clist=[r]
    # for k in NearFacilityList[u]:
    #    if centersID[k]<0: continue
    #    if k not in clist: clist.append(k)
    #    if len(clist)==n: break
    # return clist
    # if objective_overload>0: ???
    u = seed
    if u < 0: u = random.randint(0, num_units - 1)
    r = node_groups[u]
    if location_problem == 0 and objective_overload > 0:  # SAP
        rlist = [k for k in range(num_districts) if district_info[k][4] > 0]
        random.shuffle(rlist)
        r = rlist[0]
        u = nearCustomer[r]
        return NearFacilityList[u][:n]

    clist = [r]
    if random.random() > -0.5:
        for k in NearFacilityList[u]:
            if centersID[k] < 0: continue
            if k == r: continue
            clist.append(k)
            if len(clist) == n: break
        # clist.sort()
        return clist

    for i in facility_neighbors[r]:
        if centersID[i] < 0: continue
        clist.append(i)
        if len(clist) >= n: break
    # clist.sort()
    return clist


def sscflpr_sub_model(max_radius2, max_radius, cover_pecentage, time_limit, mipgap):
    # may be more facility needed, due to the covering constraint
    global centersID
    global node_groups
    rand = 0
    dlist = []
    ulist = []
    if random.random() > 0.5: rand = 00
    nf = sum(1 for x in range(num_districts) if centersID[x] >= 0)
    u = -1
    ulist = []
    if random.random() > 0.33:
        ulist = [x for x in range(num_units) if nodedij[x][node_groups[x]] > max_radius2 and nodes[x][3] > 0]
        if len(ulist) == 0:
            rlist = [x for x in range(num_districts) if centersID[x] >= 0 and district_info[x][4] > 0]
            ulist = [x for x in range(num_units) if node_groups[x] in rlist]
        if len(ulist) > 0:
            random.shuffle(ulist)
            u = ulist[0]
    # dlist=select_region(u)
    # dlist=select_region_adaptive(u)
    if random.random() > 0.5:
        # dlist=select_region_verylarge(u)
        dlist = select_region(u)
        ulist = [x for x in range(num_units) if nodes[x][3] > 0 and node_groups[x] in dlist]
        cloclist = get_cand_cflpr_locations(dlist, ulist, 1.0, max_radius2)
    else:
        dlist = select_region_adaptive(u)
        ulist = [x for x in range(num_units) if nodes[x][3] > 0 and node_groups[x] in dlist]
        cloclist = get_cand_cflpr_locations(dlist, ulist, 1.0, max_radius2)
    centers = []
    for clist in cloclist:
        tblist = list(set(clist + dlist))
        tblist.sort()
        centers = tblist
        break
    # print [len(dlist),len(centers),len(ulist)],
    exist_facility = [x for x in range(num_districts) if
                      centersID[x] >= 0 and x not in centers and facilityCapacity[x] - district_info[x][1] > 0]
    exist_facility = []
    # [x for x in range(num_districts) if centersID[x]>=0 and x not in dlist and facilityCapacity[x] > district_info[x][1]]
    prob = pulp.LpProblem("pcp", pulp.LpMinimize)
    xvariables = {}
    costs = {}

    penalty = current_penalty(max_radius2, max_radius, cover_pecentage)
    # print int(penalty),

    for i in ulist:
        for j in centers:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpBinary)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]  # *nodedij[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
            if rand == 1: costs["x_" + str(i) + "_" + str(j)] *= (29.5 + random.random()) / 30
        for j in exist_facility:
            xvariables["x_" + str(i) + "_" + str(j)] = pulp.LpVariable("x_" + str(i) + "_" + str(j), 0, 1,
                                                                       pulp.LpBinary)
            costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j]
            if nodedij[i][j] > max_radius2:
                costs["x_" + str(i) + "_" + str(j)] = nodedik[i][j] + nodes[i][3] * penalty * 2
            if rand == 1: costs["x_" + str(i) + "_" + str(j)] *= (29.5 + random.random()) / 30
    yvariables = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
        costs["y_" + str(i)] = facilityCost[i]
        if rand == 1:
            costs["y_" + str(i)] *= (29.5 + random.random()) / 30
    zvariable = pulp.LpVariable("z", 0, None, pulp.LpContinuous)
    z2variables = {}
    for i in centers:
        z2variables["z2_" + str(i)] = pulp.LpVariable("z2_" + str(i), 0, None, pulp.LpInteger)
    obj = ""
    for x in yvariables:
        obj += costs[x] * yvariables[x]
    for i in ulist:
        for j in centers:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            obj += costs["x_" + str(i) + "_" + str(j)] * xvariables["x_" + str(i) + "_" + str(j)]
    for x in z2variables:
        obj += penalty * z2variables[x]
    obj += penalty * zvariable  # 100*100000000*zvariable #*sum(facilityCost)/num_districts*zvariable
    prob += obj

    for i in ulist:
        s = ""
        for j in centers:
            s += xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            s += xvariables["x_" + str(i) + "_" + str(j)]
            # v="x_" +str(i)+ "_"+ str(j)
            # if v in xvariables : s+=xvariables[v]
        prob += s == 1

    for k in centers:
        s = ""
        for i in ulist:
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
        s -= facilityCapacity[k] * yvariables["y_" + str(k)]
        s -= z2variables["z2_" + str(k)]
        prob += s <= 0

    for k in centers:
        s = z2variables["z2_" + str(k)]
        s -= facilityCapacity[k] * yvariables["y_" + str(k)]
        prob += s <= 0

    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    for k in exist_facility:
        s = ""
        for i in ulist:
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(k)]
            # v="x_" +str(i)+ "_"+ str(k)
            # if v in xvariables: s+=nodes[i][3]*xvariables[v]
        prob += s <= facilityCapacity[k] - district_info[k][1]

    total_cover1 = 0
    total_cover2 = 0
    for i in range(num_units):
        if nodedij[i][node_groups[i]] > max_radius: continue
        if i in ulist:
            total_cover1 += nodes[i][3]
        else:
            total_cover2 += nodes[i][3]
    min_covered = total_pop * cover_pecentage / 100 - total_cover2
    s = ""
    for i in ulist:
        for j in centers:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
        for j in exist_facility:
            if nodedij[i][j] > max_radius: continue
            s += nodes[i][3] * xvariables["x_" + str(i) + "_" + str(j)]
    s += zvariable
    prob += s >= min_covered

    s = ""
    for x in yvariables: s += yvariables[x]
    numf = sum(1 for x in centersID if x >= 0)
    if adaptive_number_of_facilities == 0:
        if numf == max_num_facility:
            prob += s == len(dlist)
    else:
        soft_demand = objective_overload
        soft_demand += sum([nodes[x][3] for x in range(num_units) if nodedij[x][node_groups[x]] > max_radius2])
        covered = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] < max_radius:
                covered += nodes[i][3]
        soft_demand += max(0, total_pop * cover_pecentage / 100 - covered)
        if soft_demand == 0:
            prob += s >= len(dlist) - 1
            prob += s <= len(dlist) + 1
        elif soft_demand <= total_pop / nf / 100:
            prob += s >= len(dlist) - 1
            prob += s <= len(dlist) + 1
        elif soft_demand <= total_pop / nf:
            prob += s >= len(dlist)
            prob += s <= len(dlist) + 2
        else:
            prob += s <= len(dlist) + 2
    prob.writeLP("_SSCFLP.lp")
    initvalues = loc_sub_mst(dlist, ulist)
    for x, v in initvalues:
        if x.find("x") == 0:  xvariables[x].setInitialValue(v)
        if x.find("y") == 0:  yvariables[x].setInitialValue(v)
    # warmStart=True,
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap),
                                                        'set mip tolerances absmipgap 100', 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, warmStart=True, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("MIPGapAbs", gap * objective),
                                               ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved... or infeasible, msg={0}".format(prob.status))
        prob.writeLP("_sscflpr_sub_model.lp")
        return []
    # print [x for x in range(num_districts) if centersID[x]>=0]
    nf = 0
    nlist = []
    obj1 = 0.0
    for x in ulist: obj1 += nodedik[x][node_groups[x]]
    for x in dlist: centersID[x] = -1
    for x in ulist: node_groups[x] = -1
    for v in prob.variables():
        if (v.varValue >= 0.9):
            if v.name == "z": continue
            if v.name == "z2": continue
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
                nlist.append(i)
                nf += 1
            if items[0] == 'x':
                node_groups[i] = int(items[2])
    # print dlist
    # print centers
    # print [x for x in range(num_districts) if centersID[x]>=0]
    s = [len(dlist), len(centers), nf]
    return 1


def pop_selection(population):
    population1 = copy.deepcopy(population)
    population1.sort(key=lambda x: x[0])
    population2 = []  # delete identical solution
    # sol=[best_biobjective_global,best_centersID_global[:],best_solution_global[:],best_objective_global,best_objective_fcost_global,best_overload_global,0]
    # population2.append(copy.deepcopy(sol))
    population2.append(copy.deepcopy(population1[0]))
    sdiff = 1
    if location_problem == 3:
        sdiff = max_num_facility * 5 / 100
        if sdiff <= 5: sdiff = 5

    for x in population1:
        issimilar = 0
        for y in population2:
            rlist = [i for i in range(num_districts) if x[1][i] != y[1][i]]
            if len(rlist) >= sdiff:
                continue
            else:
                if location_problem >= 1:
                    issimilar = 1
                    break
            ulist = [i for i in range(num_units) if x[2][i] != y[2][i]]
            # diffpop=sum(nodes[i][3] for i in ulist)
            # if len(ulist)<min(num_units*1.0/num_districts,num_units/30.0) and diffpop*100.0/total_pop < min(3.0,100.0/num_districts): #100.0/num_districts: #<5%
            # print len(ulist),
            if len(ulist) < num_units * (solution_similarity_limit / 100.0):
                issimilar = 1
                break
        if issimilar == 0:
            population2.append(copy.deepcopy(x))
        if len(population2) >= max(multi_start_count * 2, 10):
            break
    return population2


def spp_mst():
    vars = []
    num_pool = len(region_pool)
    for k in range(num_districts):
        ulist = [x for x in range(num_units) if node_groups[x] == k]
        for i in range(num_pool):
            if ulist == region_pool[i][0] and region_pool[i][4] == k:
                vars.append([i, 1])
                break
    return vars


def cflpr_scp_model(maxr2, maxr, cover_pecentage, maxtime, mipgap):  # bug, the covering constraint
    global node_groups
    global centersID
    if len(region_pool) <= 10:
        arcpy_print("len(region_pool)<=10,{0}".format(len(region_pool)))
        return 0
    penalty = 100000000
    prob = pulp.LpProblem("sdp_spp", pulp.LpMinimize)
    variables = []
    costs = []
    for i in range(len(region_pool)):
        x = pulp.LpVariable("x_" + str(i), 0, 1, pulp.LpBinary)
        variables.append(x)
        cost = region_pool[i][1] + region_pool[i][3] * penalty
        if fixed_cost_obj == 1:
            k = region_pool[i][4]
            cost += facilityCost[k]
        costs.append(cost)
    zvariables = []
    for i in range(num_units):
        x = pulp.LpVariable("z_" + str(i), 0, 1, pulp.LpBinary)
        zvariables.append(x)
    obj = ""
    for i in range(len(region_pool)):
        obj += costs[i] * variables[i]
    prob += obj

    for i in range(num_units):
        s = ""
        for idx in range(len(region_pool)):
            if i in region_pool[idx][0]:
                s += variables[idx]
        if spatial_contiguity == 0:
            prob += s >= 1
        else:
            prob += s == 1

    for i in range(num_units):
        s = ""
        for idx in range(len(region_pool)):
            if i in region_pool[idx][0]:
                k = region_pool[idx][4]
                if nodedij[i][k] <= maxr: s += variables[idx]
        if spatial_contiguity == 0:
            prob += s - zvariables[i] >= 0
        else:
            prob += s - zvariables[i] == 0

    for i in range(num_units):
        s = ""
        for idx in range(len(region_pool)):
            if i in region_pool[idx][0]:
                k = region_pool[idx][4]
                if nodedij[i][k] <= maxr2:
                    s += variables[idx]
        prob += s >= 1

    if spatial_contiguity == 0:
        for k in range(num_districts):
            s = ""
            for i in range(len(region_pool)):
                if region_pool[i][4] != k: continue
                s += variables[i]
            if len(s) > 0: prob += s <= 1

    for k in range(num_districts):
        if k not in facility_inclusion_list: continue
        s = ""
        for i in range(len(region_pool)):
            if region_pool[i][4] != k: continue
            s += variables[i]
        if len(s) > 0: prob += s == 1
    if adaptive_number_of_facilities == 0:
        for i in range(len(region_pool)):
            s += variables[i]
        prob += s == max_num_facility
    s = ""
    for i in range(num_units):
        s += nodes[i][3] * zvariables[i]
    maxc = total_pop * cover_pecentage / 100
    prob += s >= maxc

    prob.writeLP("_sclp.lp")
    # mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

    vars = spp_mst()
    for x, v in vars: variables[x].setInitialValue(v)
    solver = 0
    if mip_solver == 'cbc':  # solver_message #'set emphasis mip 3','set threads 4',
        solver = pulp.apis.COIN_CMD(timeLimit=maxtime, mip=1, msg=solver_message, gapRel=mipgap,
                                    options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':  # solver_message #'set emphasis mip 3','set threads 4',
        solver = pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message, warmStart=True, timeLimit=maxtime,
                                               options=['set parallel -1', 'set mip tolerances mipgap ' + str(mipgap)])
    if mip_solver == 'gurobi':  # solver_message #'set emphasis mip 3','set threads 4',
        solver = pulp.apis.GUROBI_CMD(msg=solver_message, warmStart=True,
                                      options=[("MIPGap", mipgap), ("TimeLimit", maxtime)])
    solver.setTmpDir()  # =mip_file_path
    solver.actualSolve(prob)
    # if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
    if prob.status <= 0:
        arcpy_print("no solution! prob.status<=0...")
        return prob.status  # failer
    node_groups = [-1 for x in range(num_units)]
    centersID = [-1 for x in range(num_districts)]
    for v in prob.variables():
        if (v.varValue >= 0.99):
            items = v.name.split('_')
            if items[0] != "x": continue
            i = int(items[1])
            k = region_pool[i][4]
            # print k,costs[i],facilityCost[k]
            centersID[k] = facilityCandidate[k]
            for x in region_pool[i][0]:
                node_groups[x] = k
    # a=[ x for x in centersID if x>=0]
    # print "spp locs:",len(a),a
    update_district_info()
    # for i in range(num_districts):
    #    if district_info[i][1] >0: print i,district_info[i],facilityCost[i]
    # print
    return 1  # success


def frag_unit_minority(ulist):
    final_list = []
    ulist2 = ulist[:1]
    ulist1 = ulist[1:]
    total_area = sum(x[3] for x in nodes)
    while 1:
        for x in ulist2:
            for i in range(len(ulist1)):
                if ulist1[i] == -1: continue
                if ulist1[i] in node_neighbors[x]:
                    ulist2.append(ulist1[i])
                    ulist1[i] = -1
            ulist1 = [x for x in ulist1 if x >= 0]
        final_list.append([len(ulist2), ulist2[:]])
        if len(ulist1) <= 1:
            if len(ulist1) == 1:
                final_list.append([1, ulist1[:]])
            break
        u = ulist1[0]
        ulist2 = [u]
        del ulist1[0]
    if len(final_list) == 1: return []
    final_list.sort(key=lambda x: x[0])
    # del final_list[-1]
    flist = []
    n = total_area * spatial_contiguity_minimum_percentage / max_num_facility / 100
    for x in final_list:
        area = sum(nodes[i][3] for i in x[1])
        if area > n: continue
        flist += x[1]
    # print [len(flist),len(ulist)],
    return flist


# check continuality of a region (rid) in solution (sol)
def check_continuality_feasibility(sol, rid):
    global time_check
    global check_count
    if spatial_contiguity == 0: return 9
    # if geo_instance==0: return -1
    u = facilityCandidate[rid]
    check_count += 1
    t = time.time()
    ulist1 = [x for x in range(num_units) if sol[x] == rid and x != u]
    ulist2 = [u]
    # ulist2.append(ulist1.pop())
    for x in ulist2:
        for i in range(len(ulist1)):
            j = ulist1[i]
            if j in node_neighbors[x]:
                ulist2.append(j)
                ulist1[i] = -1
        ulist1 = [x for x in ulist1 if x >= 0]
    if len(ulist1) == 0:
        time_check += time.time() - t
        return 1  # feasible
    if spatial_contiguity == 2:
        ulist = [x for x in range(num_units) if sol[x] == rid]
        flist = frag_unit_minority(ulist)
        if flist == []:
            time_check += time.time() - t
            return 2
    time_check += time.time() - t
    return 0  # infeasible


# check continuality of a solution (sol)
def check_solution_continuality_feasibility(sol):
    if spatial_contiguity == 0: return 9
    feasible = spatial_contiguity
    for i in range(num_districts):
        if centersID[i] < 0: continue
        if check_continuality_feasibility(sol, i) <= 0:
            feasible = 0  # infeas.
            break
    return feasible


# read instance file, f1:unit info, f2: connectivity info
# 进入主要函数
def readfile(f1, f2):
    arcpy_print("enter-readfile")
    global num_units
    global total_pop
    global total_supply
    global nodes
    global node_neighbors
    global nodedij
    global nodedik
    global centersID
    global facilityCandidate
    global facilityCapacity
    global facilityCost
    global num_facilityCandidate
    global num_districts
    global district_info
    global avg_dis_min
    global potential_facilities
    global facility_inclusion_list
    node = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    # school_nodes = []
    nodes = []
    # nodes.append(node)
    arcpy_print("reading nodes ...")
    f = open(f1)
    line = f.readline()  # OID    pop    PointX    PointY    fcadidature    fcost    fcapacity
    line = f.readline()
    nodeidx = 0
    while line:
        line = line[0:-1]
        # print line
        items = line.split(',')
        if len(items) <= 2:
            items = line.split('\t')
        unit = [nodeidx, float(items[2]), float(items[3]), int(items[1]), int(items[0]), int(items[6]), int(items[4]),
                float(items[5])]
        nodes.append(unit)
        nodeidx += 1
        # nodes.append([int(items[1]), float(items[8]), float(items[9]), int(items[5]), int(items[6]), int(items[7]),int(items[12]),int(items[13])])
        line = f.readline()
    f.close()
    num_units = len(nodes)
    total_pop = sum(x[3] for x in nodes)
    ##noprint num_units,"units"
    ##noprint "reading connectivity ...",
    ###id1,id2#####
    node_neighbors = [[] for x in range(len(nodes))]
    if f2 != "na":
        # connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
        f = open(f2)
        line = f.readline()
        line = f.readline()
        links = 0
        while line:
            items = line.split(',')
            if len(items) <= 2:
                items = line.split('\t')
            if int(items[1]) != int(items[2]):
                id1 = int(items[1])
                id2 = int(items[2])
                idx1 = -1
                idx2 = -1
                for i in range(num_units):
                    if nodes[i][4] == id1:
                        idx1 = i
                    if nodes[i][4] == id2:
                        idx2 = i
                    if idx1 >= 0 and idx2 > 0:
                        break
                node_neighbors[idx1].append(idx2)
                node_neighbors[idx2].append(idx1)
                # connectivity[idx1][idx2]=1
                # connectivity[idx2][idx1]=1
                links += 1
            line = f.readline()
        f.close()
    ##noprint links,"links"
    num_units = len(nodes)
    facilityCandidate = []
    facilityCapacity = []
    facilityCost = []
    centersID = []
    arcpy_print("all data are read!")
    for i in range(num_units):
        if nodes[i][5] > 0 or all_units_as_candadate_locations == 1:
            facilityCandidate.append(i)
            facilityCapacity.append(nodes[i][5])
            facilityCost.append(nodes[i][7])
            centersID.append(i)
    num_facilityCandidate = len(facilityCandidate)
    num_districts = len(facilityCandidate)
    # facilityCandidate.sort()
    total_supply = sum(facilityCapacity)
    centersID = facilityCandidate[:]
    facility_inclusion_list = []
    for k in range(num_districts):
        u = facilityCandidate[k]
        if nodes[u][6] == 1:
            facility_inclusion_list.append(k)
    arcpy_print("existing facilities:{0}".format(facility_inclusion_list))
    nodedij = [[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
    max_dij = 0.0
    arcpy_print("craeating distance matrix......")
    for i in range(num_units):
        for k in range(num_districts):
            j = facilityCandidate[k]
            d2 = pow(nodes[i][1] - nodes[j][1], 2)
            d2 += pow(nodes[i][2] - nodes[j][2], 2)
            d = pow(d2, 0.5) / 1000
            nodedij[i][k] = d
            if d > max_dij:
                max_dij = d
    ''' 
    if len(node_neighbors)>0:
        for i in range(len(nodes)):
            for j in range(len(nodes)):
                if j<=i:
                    continue
                if connectivity[i][j]==1:
                    node_neighbors[i].append(j)
                    node_neighbors[j].append(i)'''

    district_info = [[0, 0.0, 0.0, 0.0, 0.0] for x in range(num_districts)]
    dis = 0.0
    for i in range(num_units):
        d = min(nodedij[i])
        dis += d * nodes[i][3]
    avg_dis_min = dis / total_pop
    # weighted cost from i to k

    nodedik = [[nodedij[y][x] * nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
    find_NearFacilityList(num_districts)
    arcpy_print("find_near_customer()...")
    find_near_customer()
    # find_nearFacilityFacility()
    # print("create_facility_neighbors()...")
    # 没有处理，直接return,20230213
    # create_facility_neighbors()
    potential_facilities = [x for x in range(num_districts)]
    arcpy_print("M N:{0}_{1}".format(str(num_districts),str(num_units)))
    arcpy_print("Total demand & supply:{0}_{1}_{2}".format(str(total_pop) , str(total_supply) , str(sum(facilityCost))))
    arcpy_print("end-readfile")

def clscp_mip_model_init2(maxr2, maxr, cover_pecentage, time_limit, mipgap):
    global centersID
    global node_groups
    global district_info
    prob = pulp.LpProblem("_clscp", pulp.LpMinimize)
    centers = range(num_districts)  # facilityCandidate
    sampling = 0
    if total_supply > 10 * total_pop:
        sampling = 1
        min_nf = total_pop * num_districts / total_supply
        centers = k_medoids_cflpr_sampling(min_nf * 10)
        centers = list(set(centers + facility_inclusion_list))
    covered_units = [[] for x in range(num_districts)]
    covered_cost = [facilityCost[x] for x in range(num_districts)]
    for k in range(num_districts):
        covered = []
        if k not in centers: continue
        supply = facilityCapacity[k] * 1.15  # pie*r*r / 2.6*r*r = pie/2.6=
        if sampling == 0:
            supply = facilityCapacity[k] * (1.15 + random.random() / 20)  # pie*r*r / 2.6*r*r = pie/2.6=
        cost = 0.0
        for i in nearCustomers[k]:
            if nodedij[i][k] > maxr2: break
            if supply < nodes[i][3]: break
            supply -= nodes[i][3]
            covered.append(i)
            cost += nodedik[i][k]
        covered_units[k] = covered[:]
        covered_cost[k] += cost
    avg_covered_cost = sum(covered_cost) / num_districts
    ulist = range(num_units)
    yvariables = {}
    for i in centers:
        yvariables["y_" + str(i)] = pulp.LpVariable("y_" + str(i), 0, 1, pulp.LpBinary)
    zvariables = {}
    for i in ulist:
        zvariables["z_" + str(i)] = pulp.LpVariable("z_" + str(i), 0, 1, pulp.LpInteger)
    obj = ""
    for k in centers:
        obj += covered_cost[k] * yvariables["y_" + str(k)]
    prob += obj
    s = ""
    for k in centers:
        s += facilityCapacity[k] * yvariables["y_" + str(k)]
    prob += s >= total_pop

    for k in centers:
        if k in facility_inclusion_list:
            prob += yvariables["y_" + str(k)] == 1

    if adaptive_number_of_facilities == 0:
        s = ""
        for k in centers:
            s += yvariables["y_" + str(k)]
        prob += s == max_num_facility

    for i in ulist:
        s = ""
        for j in centers:
            if nodedij[i][j] > maxr: continue
            if i in covered_units[j]:
                s += yvariables["y_" + str(j)]
        s -= zvariables["z_" + str(i)]
        prob += s >= 0

    for i in ulist:
        s = ""
        for j in centers:
            if i in covered_units[j]:
                s += yvariables["y_" + str(j)]
        prob += s >= 1

    if cover_pecentage >= 99:
        for i in ulist:
            prob += zvariables["z_" + str(i)] == 1
    else:
        s = ""
        for i in ulist:
            s += nodes[i][3] * zvariables["z_" + str(i)]
        prob += s >= total_pop * cover_pecentage / 100.0
    prob.writeLP("_sclp_init3.lp")
    gap = mipgap
    solver = ""
    if mip_solver == 'cbc':
        solver = pulp.apis.COIN_CMD(mip=1, msg=solver_message, gapRel=gap, options=['vnd on', 'node hybrid', 'rens on'])
    if mip_solver == 'cplex':
        solver = pulp.apis.cplex_api.CPLEX_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                               options=['set mip tolerances mipgap ' + str(gap), 'set parallel -1'])
    if mip_solver == 'gurobi':
        solver = pulp.apis.GUROBI_CMD(mip=1, msg=solver_message, timeLimit=time_limit,
                                      options=[("MIPGap", gap), ("TimeLimit", time_limit)])
    solver.setTmpDir()
    solver.actualSolve(prob)
    if prob.status <= 0:
        arcpy_print("model unsolved...8")
        return 0
    centersID = [-1 for x in range(num_districts)]
    node_groups = [-1 for x in range(num_units)]
    fselected = []
    for v in prob.variables():
        if (v.varValue >= 0.90):
            items = v.name.split('_')
            i = int(items[1])
            if items[0] == 'y':
                centersID[i] = facilityCandidate[i]
                fselected.append(i)
    for k in fselected:
        for i in covered_units[k]:
            if node_groups[i] == -1: node_groups[i] = k
            if node_groups[i] >= 0:
                k2 = node_groups[i]
                if nodedij[i][k] < nodedij[i][k2]: node_groups[i] = k
    update_district_info()
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0:
                continue
            if facilityCapacity[k] - district_info[k][1] >= nodes[i][3]:
                node_groups[i] = k
                district_info[k][1] += nodes[i][3]
                break
    ulist = [x for x in range(num_units) if node_groups[x] == -1]
    random.shuffle(ulist)
    for i in ulist:
        for k in NearFacilityList[i]:
            if centersID[k] < 0:
                continue
            node_groups[i] = k
            # print "&",
            break
    update_district_info()
    return 1


##LBc << LBr, constrained by radius, using SCLP to generate solutions.
##LBc >> LBr, constrained by capacity, using cSCLP to generate solutions.
##LBc == LBr, constrained by both radius and capacity? using cSCLP to generate solutions? drop???
def cflpr_matheuristic(max_radius, radius_preference, cover_pecentage, multi_start, maxloops):
    global best_objective
    global best_biobjective
    global best_objective_overload
    global best_biobjective_global
    global best_centersID_global
    global best_solution_global
    global objective
    global biobjective
    global objective_overload
    global node_groups
    global centersID
    global district_info
    global facilityCost
    # global node_neighbors
    global region_pool
    global pool_index
    global is_spp_modeling
    global all_solutions
    global max_loops_solution_not_improved
    global multi_start_count
    global solver_message
    global pop_dis_coeff
    global cflp_max_service_radius
    global cflp_service_radius_preference
    global cflp_min_service_coverage_percentage

    initialize_instance()
    max_loops_solution_not_improved = maxloops
    multi_start_count = multi_start
    arcpy_print("num_facility:{0}".format(max_num_facility))
    pop_dis_coeff = 100000000 * 1000.0 / total_pop
    covered_demand_nodes = []
    opt_radius = [0.0 for x in range(num_districts)]
    cflp_max_service_radius = max_radius
    cflp_service_radius_preference = radius_preference
    cflp_min_service_coverage_percentage = cover_pecentage

    all_solutions = []
    region_pool = []
    t = time.time()
    best_biobjective_global = MAXNUMBER
    best_biobjective = MAXNUMBER
    district_info = [[0, 0.0, 0, 0, 0] for x in range(num_districts)]
    population = []  # all
    pool_index = [[] for x in range(num_districts)]
    if sum(facilityCost) < 1:
        for x in range(num_districts):
            facilityCost[x] = 100000000
    not_improved_global = 0
    init_methods = [0, 1, 2, 3, 4]  # [1,2,4] #SCLP, CSCLP, Drop
    if adaptive_number_of_facilities == 0: init_methods = [1, 2]
    loops = multi_start_count
    for idx in range(loops):
        init_t = time.time()
        if initial_solution_method < 0:
            nm = len(init_methods)
            method = init_methods[idx % nm]
            # method=idx%5
        else:
            method = initial_solution_method
            if method > 4: method = 4
        if method == 0:
            sta = lscp_mip_model_init(radius_preference, cover_pecentage, 100, 0.002)
            if sta < 1: drop_method_cflpr(max_radius, radius_preference, cover_pecentage)
        if method == 1:
            sta = clscp_mip_model_init(radius_preference, cover_pecentage, 100, 0.01)
            if sta < 1: drop_method_cflpr(max_radius, radius_preference, cover_pecentage)
        if method == 2:
            sta = clscp_mip_model_init2(max_radius, radius_preference, cover_pecentage, 100, 0.01)
            if sta < 1: drop_method_cflpr(max_radius, radius_preference, cover_pecentage)
        if method == 3:
            sta = lscp_mip_model_init(max_radius, 99, 100, 0.002)
            if sta < 1: drop_method_cflpr(max_radius, 99, cover_pecentage)
        if method == 4:
            sta = drop_method_cflpr(max_radius, radius_preference, cover_pecentage)
        update_zero_demand()
        # check_required_facility()
        update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
        assign_CFLPr1(max_radius, radius_preference, cover_pecentage)
        assign_CFLPr2(max_radius, radius_preference, cover_pecentage)
        assign_CFLPr3(max_radius, radius_preference, cover_pecentage)
        # while one_unit_move_cflpr(max_radius,radius_preference,cover_pecentage):
        #    pass
        coverdemand = 0
        coverdemand2 = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= radius_preference: coverdemand += nodes[i][3]
            if nodedij[i][k] > max_radius: coverdemand2 += nodes[i][3]
        cp = coverdemand * 1.0 / total_pop
        penalty_demand = objective_overload + coverdemand2 + max(total_pop * cover_pecentage / 100 - coverdemand, 0)
        penalty = 100 * sum(facilityCost) / sum(facilityCapacity)
        # penalty=current_penalty(max_radius,radius_preference,cover_pecentage)
        obj = objective + objective_fcost + penalty_demand * penalty
        nf = sum(1 for x in centersID if x >= 0)
        update_region_pool_all()
        update_best_solution()
        arcpy_print("init. sol.idx{0},method{1},nf{2},biobjective{3},objective{4},objective_overload{5},coverdemand2{6},int_cp{7},time{8}".format(idx, method, nf, biobjective, objective, objective_overload, coverdemand2,int(cp * 100) / 100.0, time.time() - t))
        population.append([obj, centersID[:], node_groups[:], objective, objective_fcost, objective_overload, 0])
    population.sort(key=lambda x: x[0] + x[-1] * 10000)
    all_solutions = population
    loop = -1
    while 1:
        r = random.random()
        sidx = int(min(multi_start_count - 1, len(population)) * pow(r, 1.5) * 0.999)
        node_groups = population[sidx][2][:]
        centersID = population[sidx][1][:]
        update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
        bnf = sum(1 for x in centersID if x >= 0)
        orgs = str(bnf) + " " + str(int(biobjective)) + " " + str(int(objective)) + " " + str(
            objective_overload) + " -> "
        obj_old = biobjective
        loop += 1
        not_improved_global += 1
        obj = best_biobjective_global
        t_mip = time.time()
        r = random.random()
        '''s="N"
        if not_improved_global>max_loops_solution_not_improved/5 and random.random()>0.5: 
            ruin_idx=assign_ruin_recreate(-1)
            #assign_CFLPr1(max_radius,radius_preference,cover_pecentage)
            #assign_CFLPr2(max_radius,radius_preference,cover_pecentage)
            #assign_CFLPr3(max_radius,radius_preference,cover_pecentage)
            s="R"
            update_cflpr_district_info(max_radius,radius_preference,cover_pecentage)
        print s, '''
        if r < 0.33:
            sscflpr_sub_assign_model(max_radius, radius_preference, cover_pecentage, 10, 0.000000001)
            update_zero_demand()
            update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
            arcpy_print("ASG{0}".format(sidx))
        elif r < -0.66:
            cflpr_sub_model(max_radius, radius_preference, cover_pecentage, 10, 0.0000000001)
            update_zero_demand()
            update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
            arcpy_print("LA1{0}".format(idx))
        else:
            sscflpr_sub_model(max_radius, radius_preference, cover_pecentage, 10, 0.000000001)  # 20s?? or 50s?
            update_zero_demand()
            update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
            arcpy_print("LA2{0}".format(sidx))
        # check_required_facility()
        update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
        objimp = obj - biobjective
        obj2 = biobjective
        assign_CFLPr1(max_radius, radius_preference, cover_pecentage)  # ??
        assign_CFLPr2(max_radius, radius_preference, cover_pecentage)  # tested
        assign_CFLPr3(max_radius, radius_preference, cover_pecentage)  # tested
        update_best_solution()
        update_region_pool_all()
        coverdemand = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= radius_preference: coverdemand += nodes[i][3]
        s = ""
        if best_biobjective_global < obj - 0.000001:  # 0.1%
            s = "*"
            impp = ((best_biobjective_global - obj) / best_biobjective_global) * 1000  # -0.1%
            not_improved_global += int(max_loops_solution_not_improved * impp)
            if not_improved_global < 0: not_improved_global = 0
        else:
            s = "-"
        bnf = sum(1 for x in best_centersID_global if x >= 0)
        s += "Loop " + str(loop) + " Best: " + str(bnf) + " " + str(int(best_biobjective_global)) + " " + str(
            int(best_objective_global)) + " " + str(int(best_overload_global))
        bnf = sum(1 for x in centersID if x >= 0)
        s += " Current: " + orgs + str(bnf) + " " + str(int(biobjective)) + " " + str(int(objective)) + " " + str(
            int(objective_fcost))
        s += " Info: " + str(not_improved_global) + " " + str(int(time.time() - t))
        coverdemand = 0
        coverdemand2 = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= radius_preference: coverdemand += nodes[i][3]
            if nodedij[i][k] > max_radius: coverdemand2 += nodes[i][3]
        cp = coverdemand * 1.0 / total_pop
        penalty_demand = objective_overload + coverdemand2 + max(total_pop * cover_pecentage / 100 - coverdemand, 0)
        s += " " + str(int(objective_overload)) + " " + str(coverdemand2) + " " + str(
            max(total_pop * cover_pecentage / 100 - coverdemand, 0)) + " " + str(int(cp * 10000) / 100.0)
        s += " " + str(int(biobjective - obj_old))
        # s+=str(cflpr_search_time)
        arcpy_print(s)
        penalty = 100 * sum(facilityCost) / sum(facilityCapacity)
        # penalty=current_penalty(max_radius,radius_preference,cover_pecentage)
        obj = objective + objective_fcost + penalty_demand * penalty
        obj = biobjective
        if biobjective < obj_old:
            if loop < multi_start_count * 2:
                del population[sidx]
            population.append([obj, centersID[:], node_groups[:], objective, objective_fcost, objective_overload, 0])
            population.sort(key=lambda x: x[0])
            population = pop_selection(population)
            all_solutions = population
        if not_improved_global >= max_loops_solution_not_improved: break
        # if time.time()-t_ga > heuristic_time_limit:  break
        # if objimp<-200000: exit()
    # post procedure
    ga_time = time.time() - t
    node_groups = best_solution_global[:]
    centersID = best_centersID_global[:]
    update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
    nf = sum(1 for x in centersID if x >= 0)
    arcpy_print("3Heuristic solution:nf{0},biobjective{1},objective_fcost{2},objective{3},objective_overload{4},ga_time{5}".format(nf, biobjective, objective_fcost, objective, objective_overload, ga_time))
    t_spp = time.time()
    if is_spp_modeling >= 1:
        arcpy_print("SPP modelling...{0}".format(str(len(region_pool))))
        sta = cflpr_scp_model(max_radius, radius_preference, cover_pecentage, ga_time / 10, 0.00000001)
        if sta > 0:
            update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
            update_best_solution()
            nf = sum(1 for x in centersID if x >= 0)
            arcpy_print("spp solution:nf{0},biobjective{1},objective_fcost{2},objective{3},objective_overload{4},averageObjective{5},time-t_spp{6}".format(nf, biobjective, objective_fcost, objective, objective_overload,
                  objective / total_pop, time.time() - t_spp))
            population.append(
                [biobjective, centersID[:], node_groups[:], objective, objective_fcost, objective_overload,
                 max(0, total_pop - objective_supply)])
    for idx in range(len(all_solutions)):
        node_groups = all_solutions[idx][2][:]
        centersID = all_solutions[idx][1][:]
        update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
        coverdemand = 0
        coverdemand2 = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= radius_preference:
                coverdemand += nodes[i][3]

        if nodedij[i][k] > max_radius:
            coverdemand2 += nodes[i][3]
            penalty_demand = objective_overload + coverdemand2 + max(total_pop * cover_pecentage / 100 - coverdemand, 0)
            penalty = max(facilityCost)
            obj = objective + objective_fcost + penalty_demand * penalty
            all_solutions[idx][0] = obj
        population.sort(key=lambda x: x[0])
        node_groups = population[0][2][:]
        centersID = population[0][1][:]
        update_cflpr_district_info(max_radius, radius_preference, cover_pecentage)
        coverdemand = 0
        for i in range(num_units):
            k = node_groups[i]
            if nodedij[i][k] <= radius_preference: coverdemand += nodes[i][3]
        nf = sum(1 for x in centersID if x >= 0)
        arcpy_print("final solution:nf{0},biobjective{1},objective_fcost{2},objective{3},objective_overload{4},averageObjective{5},coverdemand/allpop{6}".format(nf, biobjective, objective_fcost, objective, objective_overload, objective / total_pop,
              int(coverdemand * 10000 / total_pop) / 100.0))
        return [best_biobjective_global, best_objective_global, best_overload_global, centersID, best_solution_global]


def search_stat():
    return
    arcpy_print("----------------search statistics----------------------")
    arcpy_print("one unit move, move and time: " + str(count_op[0]) + ", " + str(time_op[0]))
    arcpy_print("two unit move, move and time: " + str(count_op[1]) + ", " + str(time_op[1]))
    arcpy_print("three unit move, move and time: " + str(count_op[2]) + ", " + str(time_op[2]))
    arcpy_print("location swap time: " + str(time_location[0]))
    arcpy_print("location drop time: " + str(time_location[1]))
    arcpy_print("location add time: " + str(time_location[2]))
    arcpy_print("location add-drop time: " + str(time_location[3]))
    arcpy_print("location multi-exchange time: " + str(time_location[4]))
    arcpy_print("r_r_reselect_location_pmp time: " + str(time_location[5]))
    arcpy_print("location TB heur. time: " + str(time_location[7]))
    arcpy_print("TB_Whitaker time: " + str(time_Whitaker))
    arcpy_print("location PMP sub_mip time: " + str(time_location[8]))
    arcpy_print("location CFLP sub_mip time: " + str(time_location[9]))
    arcpy_print("location PMP TB time: " + str(time_pmp_re_location))
    arcpy_print("repair time: " + str(time_repair))
    arcpy_print("check edge unit time: " + str(time_check_edge_unit))
    arcpy_print("update_centers time: " + str(time_update_centers))
    arcpy_print("spp regions: " + str(len(region_pool)))
    arcpy_print("spp pooling time: " + str(time_spp))
    arcpy_print("connectivity check time: " + str(time_check))
    arcpy_print("time for ruin and recreate: " + str(time_ruin_recreate))
    if spatial_contiguity == 1:
        sta = check_solution_continuality_feasibility(best_solution_global)
        arcpy_print("solution on continuality (0 no, 1 yes) : ", str(sta))
    arcpy_print("----------------end of search statistics----------------")


def print_equality_measures():
    maxd = 0.0
    mind = MAXNUMBER
    maxdev = 0.0
    avgd = objective / total_pop
    absdev = 0.0
    stddev = 0.0
    Theil = 0.0
    schutz = 0.0
    for i in range(num_units):
        k = node_groups[i]
        dis = nodedij[i][k]
        w = nodes[i][3]
        absdev += w * abs(dis - avgd)
        stddev += w * (dis - avgd) * (dis - avgd)
        if dis > maxd: maxd = dis
        if dis < mind: mind = dis
        if abs(dis - avgd) > maxdev: maxdev = abs(dis - avgd)
        '''if dis>0:
            a=dis*math.log(dis)-avgd*math.log(avgd)
            Theil+=w*a*a
        else:
            a=avgd*math.log(avgd)
            Theil+=w*a*a'''
        if dis > 0:
            a = math.log(dis / avgd)
            Theil += w * dis * a
        schutz += w * abs(dis - avgd)
    equality_measures = {}
    # print "Centre", maxd
    #equality_measures["Centre"] = maxd
    # print "Range",maxd-mind
    #equality_measures["Range"] = maxd - mind
    # print "MaxDev", maxdev
    #equality_measures["MaxDev"] = maxdev
    # print "MeanDev",absdev/total_pop
    equality_measures["MeanDev"] = absdev / total_pop
    # print "StdDev",math.sqrt(stddev/total_pop) #d.num_units
    equality_measures["StdDev"] = math.sqrt(stddev / total_pop)
    # print "Theil", Theil/avgd/total_pop #d.num_units
    equality_measures["Theil"] = Theil / avgd / total_pop
    Gini = 0.0
    for i in range(num_units):
        k = node_groups[i]
        d1 = nodedij[i][k]
        w1 = nodes[i][3]
        for j in range(num_units):
            k = node_groups[j]
            d2 = nodedij[j][k]
            w2 = nodes[j][3]
            Gini += w1 * w2 * abs(d1 - d2)
    # print "Gini",Gini/total_pop/total_pop/2/avgd #Gini/d.num_units/d.num_units/2/avgd
    equality_measures["Gini"] = Gini / total_pop / total_pop / 2 / avgd
    equality_measures["Schutz"] = schutz / total_pop / 2 / avgd
    return equality_measures
