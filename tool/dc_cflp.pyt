# encoding: utf-8
# @Author : Guan Yabin 20230301
# 根据DC_CFLP模型构建工具箱
# @E-mail ：guanyabin2010@163.com
import arcpy
import dccflpFun as d
import time
import sys
import codecs
reload(sys)
sys.setdefaultencoding('utf8')
import csv
import os

class Toolbox(object):
    def __init__(self):
        """Define the toolbox (the name of the toolbox is the name of the.pyt file)."""
        self.label = "DC_CFLPToolbox"
        self.alias = "DC_CFLPToolbox"
        self.tools = [Tool]
# 全局变量
shpFidList = []
shpDemandList = []
shpXList = []
shpYList = []
shpFcandList = []
shpFcostList = []
shpFcapList = []
shpDemandNumList = []
shpSupplyNumList = []
class Tool(object):
    def __init__(self):
        """Define the tool (tool name is the name of the class)."""
        self.label = "DC_CFLPTool"
        self.description = "DC_CFLPTool"
        self.canRunInBackground = False

    def getParameterInfo(self):
        """Define parameter definitions"""
        fead = arcpy.Parameter(name='fead', displayName='Demand layer', datatype=['GPFeatureLayer', 'DETextfile'],direction='Input', parameterType='Required')
        fld_demand = arcpy.Parameter(name='demand_fld', displayName='Demand field', datatype='Field', direction='Input',parameterType='Required')
        fld_demand.parameterDependencies = [fead.name]
        feas = arcpy.Parameter(name='feas', displayName='Supply layer', datatype=['GPFeatureLayer', 'DETextfile'],direction='Input', parameterType='Required')
        fld_supply = arcpy.Parameter(name='supply_fld', displayName='Supply field', datatype='Field', direction='Input',parameterType='Required')
        fld_supply.parameterDependencies = [feas.name]
        fld_supply_cand = arcpy.Parameter(name='supply_fld_cand', displayName='Supply Cand(0 or 1)', datatype='Field',direction='Input', parameterType='Required')
        fld_supply_cand.parameterDependencies = [feas.name]
        fld_supply_cost = arcpy.Parameter(name='fld_supply_cost', displayName='Supply Cost(>0)', datatype='Field',direction='Input', parameterType='Required')
        fld_supply_cost.parameterDependencies = [feas.name]
        rMax = arcpy.Parameter(name='rMax', displayName='Input MaxDistance(km)', datatype='GPLong', direction='Input',parameterType='Required')
        rRecommend = arcpy.Parameter(name='rRecommend', displayName='Input Recommend Distance(km)', datatype='GPLong',direction='Input', parameterType='Required')
        coverNum = arcpy.Parameter(name='coverNum', displayName='Input Coverage(%,>0 and <100)', datatype='GPLong',direction='Input', parameterType='Required')
        CandNumber = arcpy.Parameter(name='CandNumber', displayName='Input CandNumber(0 or >0)', datatype='GPLong',direction='Input', parameterType='Required')
        #outfileText = arcpy.Parameter(name='outfileText', displayName='Output txt', datatype='DETextfile',direction='Output', parameterType='Required')
        #outfileCandidate = arcpy.Parameter(name='outfileCandidate', displayName='Output PointLayer',datatype='DEFeatureClass', direction='Output', parameterType='Required')
        outfilePath = arcpy.Parameter(name='outfilePath', displayName='Output ResultFile Path', datatype='GPType',direction='Input', parameterType='Required')
        return [fead, fld_demand, feas, fld_supply, fld_supply_cand, fld_supply_cost, rMax, rRecommend, coverNum,CandNumber,outfilePath]
    def isLicensed(self):
        """Set whether tool is licensed to execute."""
        return True

    def updateParameters(self, parameters):
        """Modify the values and properties of parameters before internal
        validation is performed.  This method is called whenever a parameter
        has been changed."""
        return

    def updateMessages(self, parameters):
        """Modify the messages created by internal validation for each tool
        parameter.  This method is called after internal validation."""
        return

    # 0305,DCCFLP模型运行完毕，下面读取结果txt,outputText路径的txt文档，每行读取，筛选出Capa>0的最终候选点，生成点图层，保存在outputPointlayer
    # fn2 是读取路径 dataDCCFLPath 是结果输出路径,nowTimeStr是时间戳，标识每一次实验的时间，精确到秒
    # 0306 关亚宾 封装函数，根据求解结果的txt读取最终的选址点数据，生成选址点点图层，在save_sol_location_problem函数中最后调用
    # 但是一致调用失败？？暂时放弃
    def createFinallPointLayer(fn2,dataDCCFLPath,nowTimeStr):
        ref_name=arcpy.Describe(pathLayer_demand).spatialReference.factoryCode
        arcpy.AddMessage("ref_name:{0}".format(ref_name))
        sr=arcpy.SpatialReference(ref_name)
        print("sr:{0}".format(sr))
        fc=arcpy.CreateFeatureclass_management(dataDCCFLPath,nowTimeStr+"resultPoint.shp","POINT","","","",sr)
        arcpy.AddField_management(fc,"x","TEXT",50)
        arcpy.AddField_management(fc,"y","TEXT",50)
        arcpy.AddField_management(fc,"maxCapa","TEXT",50)
        arcpy.AddField_management(fc,"resultCapa","TEXT",50)
        cursor=arcpy.InsertCursor(fc)
        f = codecs.open(fn2, mode='r', encoding='utf-8') # 打开txt文件，以‘utf-8'编码读取
        line = f.readline()  # 以行的形式进行读取文件
        index=0
        while line:
            a = line.split()
            b = a[6:7]  # 这是选取需要读取的位数,第6位capa
            if("".join(b)!="Capa" and "".join(b)!="0"):
                # [u'695', u'0', u'764504.5181', u'3855870.605', u'0', u'0', u'50000', u'636', u'0.0', u'16862']
                point=arcpy.Point()
                point.X=float(a[2])
                point.Y=float(a[3])
                row=cursor.newRow()
                row.shape=point
                row.x=a[2]
                row.y=a[3]
                row.maxCapa=a[6]
                row.resultCapa=a[9]
                cursor.insertRow(row)
                index=index+1
            line = f.readline()
        f.close()
        # list1 已经存储全部的选址点，生成点图层，需要字段：FID,X,Y,maxCapa,resultCapa
        arcpy.AddMessage("leave-createFinallPointLayer,resultPoint.shp-OK")

    def execute(self, parameters, messages):
        demandLayer = parameters[0].value
        demandField = parameters[1].valueAsText
        supplyLayer = parameters[2].value
        supplyField = parameters[3].valueAsText
        supplyCand = parameters[4].valueAsText
        supplyCost = parameters[5].valueAsText
        rMax = parameters[6].valueAsText
        rCommand = parameters[7].valueAsText
        coverage = parameters[8].valueAsText
        candNumber = parameters[9].valueAsText
        outputPath = parameters[10].valueAsText
        global pathLayer_demand
        global pathLayer_supply
        global shpDemand_rows
        global shpSupply_rows
        global geometries_d
        global geometries_s
        pathLayer_demand = demandLayer
        pathLayer_supply = supplyLayer
        shpDemand_rows = arcpy.SearchCursor(pathLayer_demand)
        shpSupply_rows = arcpy.SearchCursor(pathLayer_supply)
        geometries_d = arcpy.CopyFeatures_management(pathLayer_demand, arcpy.Geometry())
        geometries_s = arcpy.CopyFeatures_management(pathLayer_supply, arcpy.Geometry())
        global shpFidList
        global shpDemandList
        global shpXList
        global shpYList
        global shpFcandList
        global shpFcostList
        global shpFcostList
        global shpFcapList
        global shpDemandNumList
        global shpSupplyNumList
        shpFidList.append("OBJECTID")
        shpDemandList.append("pop")
        shpFcandList.append("Fcand")
        shpFcostList.append("Fcost")
        shpFcapList.append("Fcap")
        shpXList.append("x")
        shpYList.append("y")    
        while True:# 1-首先增加需求点的基本数据，即居民点的数据
            global shp_row
            shp_row = shpDemand_rows.next()
            if not shp_row:
                break
            shpFidList.append(shp_row.FID)
            shpDemandList.append(int(shp_row.getValue(demandField)))
            shpFcandList.append(0)
            shpFcostList.append(0)
            shpFcapList.append(0)
            shpDemandNumList.append(0)# 仅作为计数使用
        arcpy.AddMessage("demand number:{0}".format(len(shpDemandNumList)))
        while True:# 2-接着增加公共服务设施点的数据，也即是候选点的数据
            global shp_rowSupply
            shp_rowSupply = shpSupply_rows.next()
            if not shp_rowSupply:
                break
            shpFidList.append(int(shp_rowSupply.FID) + len(shpDemandNumList))
            shpDemandList.append(0)
            shpFcandList.append(int(shp_rowSupply.getValue(supplyCand)))
            shpFcostList.append(int(shp_rowSupply.getValue(supplyCost)))
            shpFcapList.append(int(shp_rowSupply.getValue(supplyField)))
            shpSupplyNumList.append(0)
        arcpy.AddMessage("supply number:{0}".format(len(shpSupplyNumList)))
        for i in range(0, len(shpDemandNumList)):# 1-增加需求点的XY坐标，即居民点的XY坐标，点图层需要同时具有地理坐标系和投影坐标系
            cid_d=0
            cid_d = geometries_d[i].centroid
            shpXList.append(round(cid_d.X,4))
            shpYList.append(round(cid_d.Y,3))
        for i in range(0, len(shpSupplyNumList)):# 2-增加候选点的坐标
            cid_s=0
            cid_s = geometries_s[i].centroid
            shpXList.append(round(cid_s.X,4))
            shpYList.append(round(cid_s.Y,3))

        # 循环列表，按照每一行写入
        #  0303,测试完成！
        # 根据居民点图层和设施点图层，其余参数，生成数据源txt，包含的列如下：
        # OBJECTID	pop	x	y	Fcand	Fcost	Fcap
        # 增加服务设施点的数据服务，同上，增加两部分
        # 最后写入的路径需要时运行结果输出的路径
        # 读取工具箱中的所有数据，生成运行模型的数据txt文档，保存在输出路径下
        
        dataDCCFLPath = outputPath+"\\"
        arcpy.AddMessage("dataDCCFLPath:{0}".format(dataDCCFLPath))
        tData = time.localtime()
        nowTimeStr = time.strftime("%Y%m%d_%H%M%S", tData)
        with codecs.open(dataDCCFLPath + "data_DCCFLP" + nowTimeStr + ".txt", 'w', 'utf-8') as f:
            c = csv.writer(f, delimiter='\t')
            for j in range(0, len(shpFidList)):
                lineTxt = list()
                lineTxt.append(shpFidList[j])
                lineTxt.append(shpDemandList[j])
                lineTxt.append(shpXList[j])
                lineTxt.append(shpYList[j])
                lineTxt.append(shpFcandList[j])
                lineTxt.append(shpFcostList[j])
                lineTxt.append(shpFcapList[j])
                c.writerow(lineTxt)      
        fn = dataDCCFLPath + "data_DCCFLP" + nowTimeStr + ".txt"
        arcpy.AddMessage(fn)

        fn2 = "na"
        maxr = float(rCommand)
        maxr2 = float(rMax)
        maxcp = int(coverage)
        spp = 0
        """set partitioning"""
        psize = 1
        """population size"""
        maxloops = 100
        """max_loops_solution_not_improved"""
        t = 50
        """timelimit for searching"""
        nf = int(candNumber)
        n = 0
        """number of facilities, number of service areas"""
        mthd = 2
        
        def save_sol_location_problem():
            fn2 = dataDCCFLPath + "data_DCCFLP" + nowTimeStr +"_Result_"+ str(maxr2) + "_"+ str(maxr) + "_"+ str(maxcp) + "_" + str(nf) + "_" + str(int(d.biobjective)) + ".txt"  #路径修改为工具箱outputPath指定的文件夹
            arcpy.AddMessage(fn2)
            f = open(fn2, "w")
            f.write("ID\tDemand\tX\tY\tR1\tR2\tCapa\tCenter\tdist\tcovered\n")
            for i in range(d.num_units):
                s = str(d.nodes[i][4]) + "\t" + str(d.nodes[i][3]) + "\t" + str(d.nodes[i][1]) + "\t" + str(
                    d.nodes[i][2]) + "\t0\t0\t"
                k = d.node_groups[i]
                uk = d.facilityCandidate[k]
                uk = d.nodes[uk][4]
                c = 0
                if i in d.centersID:
                    k = d.centersID.index(i)
                    c = d.facilityCapacity[k]
                s += str(c)
                s += "\t" + str(uk)
                """center ID"""
                s += "\t" + str(d.nodedij[i][k])
                """distance"""
                s += "\t" + str(d.district_info[k][1]) + "\n"
                """capa"""
                f.write(s)
            f.close()
            # 0306 关亚宾增加：封装函数一致不能调用，暂时将代码直接放在这里运行
            global ref_name
            ref_name=arcpy.Describe(pathLayer_demand).spatialReference.factoryCode
            arcpy.AddMessage("ref_name:{0}".format(ref_name))
            # 进入创建选址点点图层部分
            fc=arcpy.CreateFeatureclass_management(dataDCCFLPath,nowTimeStr+"resultPoint.shp","POINT","","","",arcpy.SpatialReference(ref_name))
            arcpy.AddField_management(fc,"x","TEXT",50)
            arcpy.AddField_management(fc,"y","TEXT",50)
            arcpy.AddField_management(fc,"maxCapa","TEXT",50)
            arcpy.AddField_management(fc,"resultCapa","TEXT",50)
            cursor=arcpy.InsertCursor(fc)
            # 进入创建线图层部分，根据求解结果，居民点到公共服务设施点连线
            fcLine=arcpy.CreateFeatureclass_management(dataDCCFLPath,nowTimeStr+"resultLine.shp","POLYLINE","","","",arcpy.SpatialReference(ref_name))
            arcpy.AddField_management(fcLine,"demandID","TEXT",50)
            arcpy.AddField_management(fcLine,"xBegin","TEXT",50)
            arcpy.AddField_management(fcLine,"yBegin","TEXT",50)
            arcpy.AddField_management(fcLine,"xEnd","TEXT",50)
            arcpy.AddField_management(fcLine,"yEnd","TEXT",50)
            arcpy.AddField_management(fcLine,"demand","TEXT",50)
            arcpy.AddField_management(fcLine,"supplyId","TEXT",50)
            arcpy.AddField_management(fcLine,"dist","TEXT",50)
            cursorLine=arcpy.InsertCursor(fcLine)
            # 0306 关亚宾，定义内部函数，获取线图层的终点坐标值，循环结果txt，根据传递的参数Center和ID对比，对比成功后返回[x,y]
            def getLineEndPoint(center):
                xyEndList=[]
                file = codecs.open(fn2, mode='r', encoding='utf-8')
                lineF = file.readline()
                while lineF:
                    lineList = lineF.split()
                    # 这是选取需要读取的位数，第1位ID
                    idStr = lineList[0:1]
                    if("".join(idStr)!="ID" and "".join(idStr)==center):
                        # 比对成功，返回[x,y]
                        xyEndList.append(float(lineList[2]))
                        xyEndList.append(float(lineList[3]))
                    lineF = file.readline()
                file.close()
                return xyEndList
            # 打开求解结果txt文件，以‘utf-8'编码读取
            f = codecs.open(fn2, mode='r', encoding='utf-8')
            line = f.readline()
            while line:
                a = line.split()
                # 这是选取需要读取的位数，第6位capa
                b = a[6:7]
                if("".join(b)!="Capa" and "".join(b)!="0"):
                    # [u'695', u'0', u'764504.5181', u'3855870.605', u'0', u'0', u'50000', u'636', u'0.0', u'16862']
                    point=arcpy.Point()
                    point.X=float(a[2])
                    point.Y=float(a[3])
                    row=cursor.newRow()
                    row.shape=point
                    row.x=a[2]
                    row.y=a[3]
                    row.maxCapa=a[6]
                    row.resultCapa=a[9]
                    cursor.insertRow(row)
                # 这是选取需要读取的位数，第1位Demand人口
                c=a[1:2]
                if("".join(c)!="Demand" and "".join(c)!="0"):
                    # 获取所有的居民点数据
                    # 0	2482	754489.9455	3854902.285	0	0	0	796	1.46039228634	49186
                    array=arcpy.Array()
                    pointB=arcpy.Point()
                    pointE=arcpy.Point()
                    pointB.X=float(a[2])
                    pointB.Y=float(a[3])
                    # 需要处理终点的XY坐标
                    pointE.X=getLineEndPoint(a[7])[0]
                    pointE.Y=getLineEndPoint(a[7])[1]
                    array.add(pointB)
                    array.add(pointE)
                    polyline=arcpy.Polyline(array)
                    rowLine=cursorLine.newRow()
                    rowLine.shape=polyline
                    rowLine.demandID=a[0]
                    rowLine.xBegin=a[2]
                    rowLine.yBegin=a[3]
                    rowLine.xEnd=str(pointE.X)
                    rowLine.yEnd=str(pointE.Y)
                    rowLine.demand=a[1]
                    rowLine.supplyId=a[7]
                    rowLine.dist=str(round(float(a[8]),3))
                    cursorLine.insertRow(rowLine)
                line = f.readline()
            f.close()
            arcpy.AddMessage("created resultPoint.shp and resultLine.shp")
        d.location_problem = 1
        d.all_units_as_candadate_locations = 0
        """ d.fixed_cost_obj=01"""
        d.spatial_contiguity = 0
        d.adaptive_number_of_facilities = 1
        if nf > 0: d.adaptive_number_of_facilities = 0
        d.pop_dis_coeff = 100000
        """10000#1000000 #100000 for FLP 1-5 for PDP"""
        d.pop_deviation = 0.0
        """for PDP"""
        d.max_loops_solution_not_improved = maxloops
        """for search termination"""
        d.ruin_oprators = [1, 2]
        d.initial_solution_method = 0
        """read instance file(s)"""
        d.readfile(fn, "na")
        """read self-defined instances"""
        if fn2 != "na": d.readdistance(fn2)
        t0 = time.time()
        d.initial_solution_method = mthd
        """0,1,2"""
        """
        0 lscp(r1)
        3 lscp(r2)
        1 clscp(r1)
        2 clscp2(r2,r1)
        4 drop
        d.initial_solution_method=2 for a city with high-density poputation
        d.initial_solution_method=-1 automatically select a method
        """
        d.solution_similarity_limit = 5.0
        d.solver_message = 0
        d.max_num_facility = nf
        d.mip_solver = "gurobi"
        d.cflpr_matheuristic(maxr2, maxr, maxcp, psize, maxloops)
        save_sol_location_problem()
        d.search_stat()
        arcpy.AddMessage("=========================Final results=========================")
        arcpy.AddMessage("objective:{0}".format(d.biobjective))
        arcpy.AddMessage("facility cost:{0}".format(d.objective_fcost))
        arcpy.AddMessage("transportation cost:{0}".format(d.objective))
        arcpy.AddMessage("srrvice overload:{0}".format(d.objective_overload))
        arcpy.AddMessage("pool size:{0}".format(len(d.region_pool)))
        arcpy.AddMessage("total time:{0}".format(time.time() - t0))
        arcpy.AddMessage("facilities selected:{0}".format([x for x in d.centersID if x >= 0]))
        #arcpy.AddMessage("demand assignment:{0}".format(d.node_groups))
        #arcpy.AddMessage("service area stat:")
        for i in range(d.num_districts):
            if d.district_info[i][0] == 0: continue
            #arcpy.AddMessage("facilityCandidate[i]:{0},district_info[i]:{1},district_info[i][2] / d.district_info[i][1]:{2}".format(d.facilityCandidate[i], d.district_info[i], d.district_info[i][2] / d.district_info[i][1]))
            #arcpy.AddMessage("continuality:{0}".format(d.check_continuality_feasibility(d.node_groups, i)))
        #arcpy.AddMessage("solutions: obj, f_cost,t_cost, overload")
        for x in d.all_solutions:
            nf = sum(1 for y in x[1] if y >= 0)
            #arcpy.AddMessage("nf{0},x[3] / d.total_pop={1}, x[0]={2}, x[3]={3}, x[4]={4}, x[5]={5}".format(nf, x[3] / d.total_pop, x[0], x[3], x[4], x[5]))
            supply = sum(d.facilityCapacity[y] for y in range(d.num_districts) if x[1][y] >= 0)
            #arcpy.AddMessage(supply * 1.0 / d.total_pop)
            #arcpy.AddMessage([y for y in x[1] if y >= 0])
            covered = [0 for i in range(20)]
            #arcpy.AddMessage(covered)
            for i in range(d.num_units):
                k = x[2][i]
                dis = int(d.nodedij[i][k] * 2)
                if dis < 20:
                    covered[dis] += d.nodes[i][3]
            for i in range(1, 19):
                covered[i] += covered[i - 1]
            for i in range(20):
                if covered[i] == 0:
                    continue
                #arcpy.AddMessage([i, int(covered[i] * 10000 / d.total_pop) / 100.0])
        arcpy.AddMessage("-----------radius (km) coverage (%) statistics---------------")
        covered = [0 for x in range(200)]
        for i in range(d.num_units):
            k = d.all_solutions[0][2][i]
            dis = int(d.nodedij[i][k] * 10)
            if dis < 200: covered[dis] += d.nodes[i][3]
        for i in range(1, 199): covered[i] += covered[i - 1]
        for i in range(200):
            if covered[i] == d.total_pop: break
            if covered[i] == 0: continue
            arcpy.AddMessage("{0}{1}-{2}{3}".format(float(i + 1) / 10, "km", int(covered[i] * 1000000 / d.total_pop) / 10000.0, "%"))
        arcpy.AddMessage("---------------------------------------------------------------")
        arcpy.AddMessage("cflpr_search_time:{0}".format(d.cflpr_search_time))
        arcpy.AddMessage("cflpr_search_improves:{0}".format(d.cflpr_search_improves))
        arcpy.AddMessage("facility_inclusion_list:{0}".format(d.facility_inclusion_list))
        arcpy.AddMessage("facility_list:")
        arcpy.AddMessage([x for x in range(d.num_districts) if d.centersID[x] >= 0])
        nf = sum(1 for x in d.centersID if x >= 0)
        arcpy.AddMessage("nf:{0},avergae{1},{2},time{3}".format(nf, d.objective / d.total_pop, d.biobjective, time.time() - t0))
        for i in range(d.num_units):
            if d.nodes[i][3] == 0: continue
            k = d.node_groups[i]
            if d.nodedij[i][k] > maxr2:
                arcpy.AddMessage("nodedij[{0}][{1}]>rMax, {2}and {3}:".format(i, k, d.nodes[i][3], d.nodedij[i][k]))
        for k in d.facility_inclusion_list:
            if d.centersID[k] < 0:
                arcpy.AddMessage("required facility not selected:{0}".format(k))
        equality_measures = d.print_equality_measures()
        arcpy.AddMessage("-----------equality measures---------------")
        for x in equality_measures:
            arcpy.AddMessage("{0}-equality_measures:{1}".format(x, equality_measures[x]))
        arcpy.AddMessage("Congratulations!All of the code has run successfully!")
        return None