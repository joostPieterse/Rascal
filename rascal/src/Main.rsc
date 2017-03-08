module Main
import analysis::flow::ObjectFlow;
import lang::java::flow::JavaToObjectFlow;
import List;
import Set;
import Relation;
import lang::java::m3::Core;
import lang::java::jdt::m3::Core;

import IO;
import vis::Figure; 
import vis::Render;

alias OFG = rel[loc from, loc to];


public void main() {
	m=createM3FromEclipseProject(|project://eLib|);
	drawDiagram(m);	
	FlowProgram p = createOFG(|project://eLib|);
	methods(m);
	rel[loc from, loc to] relations = buildGraph(p);
	propTest(m,p);
}

public map[loc,loc] propTest(m,p){
	OFG g = buildFlowGraph(p);
	OFG result = prop(g,{ <r,q> | call(r,q,_,_,_) <- p.statements }+
		{<ty,ui>|newAssign(ty,ui,_,_)<-p.statements}+
		{ <c,d> | <c,d> <- m@typeDependency,/(variable|field)/:=c.scheme },{},true);
	relevantTypes = {|java+interface:///java/util/List|,|java+class:///java/util/LinkedList|,|java+interface:///java/util/Collection|,
		|java+interface:///java/util/Map|,|java+class:///java/util/HashMap|,|java+class:///java/util/ArrayList|};
	OFG relevantPart = {<a,b>|<a,b><-result,<a,c><-m@typeDependency,!/List/:=b.path, /class/:=b.scheme,c in relevantTypes};	
	map[loc, set[loc]] relevantMap = index(relevantPart);
  	map[loc,loc] locMap = (a:leastSuper(relevantMap[a],m)|a<-relevantMap);
	return locMap;
}

public set[loc] supers(loc l, M3 m) {
	p = {l};
	solve (p) {
		p = carrier({<sub,super> | <sub, super><-m@extends, sub in p});
	};
	return p + l+|java+class:///java/lang/Object|;
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

/*from https://github.com/usethesource/rascal/blob/master/src/org/rascalmpl/library/analysis/flow/ObjectFlow.rsc*/
OFG buildFlowGraph(FlowProgram p)
  = { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) }
  + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements }
  + { <y, x> | assign(x, _, y) <- p.statements}
  + { <as[i], fps[i]> | call(x, _, y, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) }
  + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements }
  + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
  ;
  
/*Implementation by Davy Landman and Jurgen Vinju (https://gist.github.com/jurgenvinju/8972255) that we can use*/
OFG buildGraph(FlowProgram p) 
  = { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) }
  + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements }
  /* + ... etc */ 
  ;
  
OFG prop(OFG g, rel[loc,loc] gen, rel[loc,loc] kill, bool back) {
  OFG IN = { };
  OFG OUT = gen + (IN - kill);
  gi = g<to,from>;
  set[loc] pred(loc n) = gi[n];
  set[loc] succ(loc n) = g[n];
  
  solve (IN, OUT) {
    IN = { <n,\o> | n <- carrier(g), p <- (back ? pred(n) : succ(n)), \o <- OUT[p] };
    OUT = gen + (IN - kill);
  }
  
  return OUT;
}

rel[&G, &T] propagate(rel[&G, &T] g, rel[&G, &T] gen, rel[&G, &T] kill, bool back) {
	rel[&G, &T] IN = {};
	rel[&G, &T] OUT = gen + (IN - kill);
	if (back) {
		g = g<1,0>;
	}
	
	solve (IN, OUT) {
		IN = g o OUT;
		OUT = gen + (IN - kill);
	}
	
	return OUT;
}

public void drawDiagram(M3 m) {
  classFigures = [box(text("<cl.path[1..]>"), id("<cl>")) | cl <- classes(m)]; 
  edges = [edge("<to>", "<from>") | <from,to> <- m@extends ];  
  
  render(scrollable(graph(classFigures, edges, hint("layered"), std(gap(10)), std(font("Bitstream Vera Sans")), std(fontSize(20)))));
}
 
public str dotDiagram(M3 m) {
  return "digraph classes {
         '  fontname = \"Bitstream Vera Sans\"
         '  fontsize = 8
         '  node [ fontname = \"Bitstream Vera Sans\" fontsize = 8 shape = \"record\" ]
         '  edge [ fontname = \"Bitstream Vera Sans\" fontsize = 8 ]
         '
         '  <for (cl <- classes(m)) { /* a for loop in a string template, just like PHP */>
         ' \"N<cl>\" [label=\"{<cl.path[1..] /* a Rascal expression between < > brackets is spliced into the string */>||}\"]
         '  <} /* this is the end of the for loop */>
         '
         '  <for (<from, to> <- m@extends) {>
         '  \"N<to>\" -\> \"N<from>\" [arrowhead=\"empty\"]<}>
         '}";
}
 
public void showDot(M3 m) = showDot(m, |home:///<m.id.authority>.dot|);
 
public void showDot(M3 m, loc out) {
  writeFile(out, dotDiagram(m));
}