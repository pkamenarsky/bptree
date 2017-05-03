function insert<K, V>(a: [K, V], as: [K, V][]): [K, V][] {
    let i = 0;
    while (i < as.length && a[0] > as[i][0]) i++;

    let as_ = as.slice();
    as_.splice(i, 0, a);
    return as_;
}

function splitAt<A>(at: number, xs: A[]): [A[], A[]] {
    return [xs.slice(0, at), xs.slice(at)];
}

function cons<A>(a: A, as: A[]): A[] {
    let as_ = as.slice();
    as_.unshift(a);
    return as_;
}

function concat<A>(a1: A[], a2: A[]): A[] {
    return a1.concat(a2);
}

function tail<A>(as: A[]): A[] {
    let as_ = as.slice();
    as_.shift();
    return as_;
}

function init<A>(as: A[]): A[] {
    let as_ = as.slice();
    as_.pop();
    return as_;
}

function last<A>(as: A[]): A {
    return as[as.length - 1];
}

function span<A>(pred: (A) => boolean, as: A[]): [A[], A[]] {
    let i = 0;
    while (i < as.length && pred(as[i])) i++;

    return splitAt(i, as);
}

// -------------------------------------------------------------------------------- 

type Ptr = number;

interface BPNode<K, V> {}

class BPLeaf<K, V> implements BPNode<K, V> {
    kvs: [K, V][];
    next: Ptr | null;

    constructor(kvs: [K, V][], next: Ptr | null) {
        this.kvs = kvs;
        this.next = next;
    }
}

class BPInternal<K, V> implements BPNode<K, V> {
    ptr: Ptr;
    children: [K, Ptr][];

    constructor(ptr: Ptr, children: [K, Ptr][]) {
        this.ptr = ptr;
        this.children = children;
    }
}

// type BPNode<K, V> = BPInternal<V> | BPLeaf<K, V>;

class BPTree<K, V> {
    backend: BPTreeBackend<K, V>;

    constructor(backend: BPTreeBackend<K, V>) {
        this.backend = backend;
    }
}

type BPTreeBackend<K, V> = {
    root: () => Ptr;
    setRoot: (ptr: Ptr) => void;

    getSize: () => number;

    getNode: (ptr: Ptr) => BPNode<K, V>;
    setNode: (ptr: Ptr, node: BPNode<K, V>) => void;

    createNode: (node: BPNode<K, V>) => Ptr;
    createRoot: (node: BPNode<K, V>) => void;

    print: () => void;
}

function printTree<K, V>(root: Ptr, kvs: { [key: number]: BPNode<K, V> }) {
    console.log(`Root: [${root}]`);

    for (let [ptr, node] of Object.entries(kvs)) {
        if (node instanceof BPInternal) {
            console.log(`[${ptr}] N: *${node.ptr} ${node.children.map(([k, v]) => "[" + k + ", *" + v + "]")}`);
        }
        else if (node instanceof BPLeaf) {
            console.log(`[${ptr}] L: ${node.kvs.map(([k, v]) => "[" + k + ", " + v + "]")}} *${node.next}`);
        }
    }
}

function memoryBackend<K, V>(size: number): BPTreeBackend<K, V> {
    let kvs = {0: new BPLeaf([], null)}, root = 0, cnt = 1;
    return {
        root: () => { return root; },
        setRoot: (ptr) => { root = ptr; },
        getSize: () => { return size; },
        getNode: (ptr) => { return kvs[ptr]; },
        setNode: (ptr, node) => { kvs[ptr] = node; },
        createNode: (node) => { kvs[cnt] = node; return cnt++; },
        createRoot: (node) => { kvs[cnt] = node; root = cnt++; },
        print: () => { printTree(root, kvs); }
    };
}

function nodesize<K, V>(node: BPNode<K, V>): number {
    if (node instanceof BPInternal) {
        return node.children.length;
    }
    else if (node instanceof BPLeaf) {
        return node.kvs.length;
    }
}

function insert_<K, V>(tree: BPTree<K, V>, k: K, v: V) {
    let rt = tree.backend.root();
    insert__(tree, rt, [], k, v);
}

function insert__<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], k: K, v: V) {
    let nd = tree.backend.getNode(node);

    if (nd instanceof BPLeaf) {
        insertLeaf(tree, node, path, k, v, nd.kvs, nd.next);
    }
    else if (nd instanceof BPInternal) {
        insertInternal(tree, node, path, k, v, nd.ptr, nd.children);
    }
}

function insertLeaf<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], k: K, v: V, kvs: [K, V][], mptr: Ptr) {
    let sz = tree.backend.getSize();

    if (kvs.length + 1 <= sz) {
        tree.backend.setNode(node, new BPLeaf(insert<K, V>([k, v], kvs), mptr));
    }
    else {
        let half = Math.floor(sz / 2);
        let [lefts, [[rk, rv], ...rights]] = splitAt(half, kvs);
        let lefts_: [K, V][], rights_: [K, V][];
        let midk: K;
        let leftnode = node;

        if (k < rk) {
            lefts_ = insert<K, V>([k, v], lefts);
            rights_ = cons<[K, V]>([rk, rv], rights);
        }
        else {
            lefts_ = concat<[K, V]>(lefts, [[rk, rv]]);
            rights_ = insert<K, V>([k, v], rights);
        }

        midk = rights_[0][0];

        let rightnode = tree.backend.createNode(new BPLeaf(rights_, mptr));
        tree.backend.setNode(leftnode, new BPLeaf(lefts_, rightnode));

        if (path.length == 0) {
            tree.backend.createRoot(new BPInternal(leftnode, [[midk, rightnode]]));
        }
        else {
            insertLink(tree, path[0], tail(path), leftnode, midk, rightnode);
        }
    }
}

function insertInternal<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], k: K, v: V, lp: Ptr, kps_: [K, Ptr][]) {
    if (kps_.length == 0) {
        insert__(tree, lp, cons(node, path), k, v);
    }
    else {
        let [[rk, rp], ...kps] = kps_;
        if (k < rk) {
            insert__(tree, lp, cons(node, path), k, v);
        }
        else {
            insertInternal(tree, node, path, k, v, rp, kps);
        }
    }
}

function insertLink<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], leftnode: Ptr, k: K, rightnode: Ptr) {
    let sz = tree.backend.getSize();
    let nd = tree.backend.getNode(node);

    if (nd instanceof BPInternal) {
        let lp = nd.ptr;
        let kps: [K, Ptr][] = nd.children;

        if (kps.length + 1 <= sz) {
            tree.backend.setNode(node, insertLinkKps(tree, nd, leftnode, k, rightnode));
        }
        else {
            let half = Math.floor(sz / 2);
            let [allllkps, [[rk, rp], ...rkps]] = splitAt<[K, Ptr]>(half, kps);
            let lkps = init(allllkps);
            let [lrk, lrp] = last(allllkps);
            let left: BPNode<K, V>, midkey: K, right: BPNode<K, V>;

            if (k < lrk) {
                left = insertLinkKps(tree, new BPInternal(lp, lkps), leftnode, k, rightnode);
                midkey = lrk;
                right = new BPInternal(lrp, cons<[K, Ptr]>([rk, rp], rkps));
            }
            else if (k > rk) {
                left = new BPInternal(lp, concat<[K, Ptr]>(lkps, [[lrk, lrp]]));
                midkey = rk;
                right = insertLinkKps(tree, new BPInternal(rp, rkps), leftnode, k, rightnode);
            }
            else {
                left = new BPInternal(lp, concat<[K, Ptr]>(lkps, [[lrk, lrp]]));
                midkey = k;
                right = new BPInternal(rightnode, cons<[K, Ptr]>([rk, rp], rkps));
            }

            let leftp = node;

            tree.backend.setNode(leftp, left);
            let rightp = tree.backend.createNode(right);

            if (path.length == 0) {
                tree.backend.createRoot(new BPInternal(leftp, [[midkey, rightp]]));
            }
            else {
                insertLink(tree, path[0], tail(path), leftp, midkey, rightp);
            }
        }
    }
}

function insertLinkKps<K, V>(tree: BPTree<K, V>, node: BPNode<K, V>, leftnode: Ptr, k: K, rightnode: Ptr): BPNode<K, V> {
    if (node instanceof BPInternal) {
        if (node.ptr === leftnode) {
            return new BPInternal(node.ptr, cons<[K, Ptr]>([k, rightnode], node.children));
        }
        else {
            let [lkps, [rkn, ...rkps]] = span<[K, Ptr]>(([_, n]) => n !== leftnode, node.children);
            return new BPInternal(node.ptr, concat<[K, Ptr]>(lkps, cons<[K, Ptr]>(rkn, cons<[K, Ptr]>([k, rightnode], rkps))));
        }
    }
}

function insequence<K, V>(tree: BPTree<K, V>): [K, V][] {
    let rt = tree.backend.root();
    return insequence_(tree, rt);
}

function insequence_<K, V>(tree: BPTree<K, V>, node: Ptr): [K, V][] {
    let nd = tree.backend.getNode(node);

    if (nd instanceof BPLeaf) {
        if (nd.next === null) {
            return nd.kvs;
        }
        else {
            return concat(nd.kvs, insequence_(tree, nd.next));
        }
    }
    else if (nd instanceof BPInternal) {
        return insequence_(tree, nd.ptr);
    }
}

function test() {
    const eqArrs = function<A>(cmp: (a: A, b: A) => boolean, a1: A[], a2: A[]): boolean {
        if (a1.length !== a2.length) {
            return false;
        }
        else {
            for (let i = 0; i < a1.length; i++) {
                if (!cmp(a1[i], a2[i]))
                    return false;
            }

            return true;
        }
    }

    end:
    for (let size = 2; size < 100; size++) {
        for (let length = 0; length < 1000; length++) {
            let be = memoryBackend<number, number>(4), tree = new BPTree(be), a: [number, number][] = [];
            for (let i = 0; i < length; i++) {
                insert_(tree, i, i);
                a.push([i, i]);
            }

            if (eqArrs(([a, b], [c, d]) => a == c && b == d, a, insequence(tree))) {
                console.log(`${size}, ${length}: OK`);
            }
            else {
                console.log(`${size}, ${length}: FAILED`);
                console.log(`Expected: ${a}`);
                console.log(`Result  : ${insequence(tree)}`);
                break end;
            }
        }
    }
}

test();
