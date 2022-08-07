
struct segment_tree{
    int n, tn; 
    vector<int> seg_t;
    segment_tree(int k){
        n= k;
        seg_t.resize(2*n+4);  
        tn= pow(2, ceil((double)log2(k)));
        seg_t.resize(tn+10);
        // it doesnt matter even if we did seg.resize(tn) as 2*n >=tn always, so it doesnt matter

    }
    void take_input(){
        for(int i=tn, j=1; j<=n; j++, i++){
            cin>>seg_t[i];
        }
    }
    void build_seg_t(){
        for(int i=2*tn-1; i>0; i-=2){
            seg_t[i/2]= max(seg_t[i], seg_t[i-1]);
        }
    }
    void update(int index, int value){
        seg_t[index+tn-1]= value;
        index+=tn-1;
        while(index!=0){
            seg_t[index/2]= max( seg_t[index], index&1? seg_t[index-1]: seg_t[index+1]);
            index/=2;
        }
    }
    void query(int cur_node, int l, int r, int start, int end, int & value){ // here l and r is our query's range
        if(start > r || end < l) return;
        else if(start >= l and end <= r){
            value= max(value, seg_t[cur_node]);
            return;
        }
        else{
            query(cur_node*2, l, r, start, start-1 + (end-start+1)/2, value);
            query(cur_node*2+1, l, r, start+ (end-start+1)/2, end, value);
        }
        return;
    }
};
