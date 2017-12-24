BEGIN {
    string f,m,def_f,def_m;
    graph_t g = graph("main","D");
    graph_t srcg,dstg;
    node_t src,dst;
    setDflt(g,"N","shape","plaintext");
    while(scanf("%s @ %s -> %s @ %s\n",&f,&m,&def_f,&def_m)>0) {
        srcg=subg(g,"cluster_"+m);
        aset(srcg,"label",m);
        src=subnode(srcg,node(g,f+"_"+m));
        aset(src,"label",f);
        
        dstg=subg(g,"cluster_"+def_m);
        aset(dstg,"label",def_m);
        dst=subnode(dstg,node(g,def_f+"_"+def_m));
        aset(dst,"label",def_f);
        
        subedge(g,edge(src,dst,""));
    };
    write(g);
}
