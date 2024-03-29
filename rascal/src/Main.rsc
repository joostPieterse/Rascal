module Main
import analysis::flow::ObjectFlow;
import lang::java::flow::JavaToObjectFlow;
import List;
import Set;
import Relation;
import lang::java::m3::Core;
import lang::java::jdt::m3::Core;

import IO;

import DateTime;

alias OFG = rel[loc from, loc to];


public map[loc,loc] saveResult(loc projectLocation) {
	m=createM3FromEclipseProject(projectLocation);
	FlowProgram p = createOFG(projectLocation);
	map[loc,loc] suggestions = getSuggestions(m,p);
	writeFile(|project://rascal/output/result.txt|,suggestions);
	return suggestions;
}

public Duration getDuration(loc projectLocation) {
	datetime startTime=now();
	saveResult(projectLocation);
	return now()-startTime;
}

public map[loc,loc] getSuggestions(m,p){
	OFG g = buildFlowGraph(p);
	OFG result = propagate(g,{ <r,q> | call(r,q,_,_,_) <- p.statements }+
		{<ty,ui>|newAssign(ty,ui,_,_)<-p.statements}+
		{ <c,d> | <c,d> <- m@typeDependency,/(variable|field)/:=c.scheme },{},true);
	relevantTypes = {|java+interface:///java/util/List|,|java+class:///java/util/LinkedList|,|java+interface:///java/util/Collection|,
		|java+interface:///java/util/Map|,|java+class:///java/util/HashMap|,|java+class:///java/util/ArrayList|,|java+class:///java/util/HashSet|,
		|java+class:///java/util/Set|};
	OFG relevantPart = {<a,b>|<a,b><-result,<a,c><-m@typeDependency,b notin relevantTypes, /class/:=b.scheme,c in relevantTypes};	
	map[loc, set[loc]] relevantMap = index(relevantPart);
  	map[loc,loc] locMap = (a:leastSuper(relevantMap[a],m)|a<-relevantMap);
	return locMap;
}

public set[loc] supers(loc l, M3 m) {
	p = {l};
	solve (p) {
		p = carrier({<sub,super> | <sub, super><-m@extends+m@implements, sub in p});
	};
	return p + l + |java+class:///java/lang/Object|;
}

public set[&T] intersect(set[set[&T]] sets) {
	set[&T] intersection = getOneFrom(sets);
	for (set[&T] s <- sets) intersection &= s;
	return intersection;
}

public loc leastSuper(set[loc] ls, M3 m) {
	set[loc] supers_l(loc l) = supers(l, m);
	set[loc] allSuper = intersect(mapper(ls, supers_l));
	return ( getOneFrom(allSuper) | size(supers_l(pl)) > size(supers_l(it)) ? pl : it | loc pl <- allSuper );
}