// TODO: must insert at right place
function insert<A>(a: A, xs: A[]): A[] {
    let xss = xs.slice();
    xss.push(a);
    return xss;
}

function splitAt<A>(at: number, xs: A[]): [A[], A[]] {
    return [[], []];
}

function cons<A>(a: A, as: A[]): A[] {
    return [];
}

function concat<A>(a1: A[], a2: A[]): A[] {
    return [];
}

function tail<A>(as: A[]): A[] {
    return [];
}

function init<A>(as: A[]): A[] {
    return [];
}

function last<A>(as: A[]): A {
    return undefined;
}

function span<A>(pred: (A) => boolean, as: A[]): [A[], A[]] {
    return [[], []];
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
    size: number;
    backend: BPTreeBackend<K, V>;
}

class BPTreeBackend<K, V> {
    root: () => Ptr;
    setRoot: (ptr: Ptr) => void;

    getSize: () => number;

    getNode: (ptr: Ptr) => BPNode<K, V>;
    setNode: (ptr: Ptr, node: BPNode<K, V>) => void;

    createNode: (node: BPNode<K, V>) => Ptr;
    createRoot: (node: BPNode<K, V>) => void;
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
        tree.backend.setNode(node, new BPLeaf(insert<[K, V]>([k, v], kvs), mptr));
    }
    else {
        let half = Math.floor(kvs.length / 2);
        let [lefts, rights] = splitAt(half - 1, kvs);
        let rk = rights[0][0], rv = rights[0][1];
        let lefts_: [K, V][], rights_: [K, V][];
        let midk: K;
        let leftnode = node;

        if (k < rk) {
            lefts_ = insert<[K, V]>([k, v], lefts);
            rights_ = cons<[K, V]>([rk, rv], rights);
        }
        else {
            lefts_ = concat<[K, V]>(lefts, [[rk, rv]]);
            rights_ = insert<[K, V]>([k, v], rights);
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

function insertInternal<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], k: K, v: V, lp: Ptr, kps: [K, Ptr][]) {
    if (kps.length == 0) {
        insert__(tree, lp, cons(node, path), k, v);
    }
    else {
        if (k < kps[0][0]) {
            insert__(tree, lp, cons(node, path), k, v);
        }
        else {
            insertInternal(tree, node, path, k, v, kps[0][1], kps);
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
            let half = Math.floor(kps.length / 2);
            let [allllkps, rkps] = splitAt<[K, Ptr]>(half - 1, kps);
            let rk = rkps[0][0];
            let rp = rkps[0][1];
            let lkps = init(allllkps);
            let lrk = last(allllkps)[0], lrp = last(allllkps)[1];
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
                tree.backend.createNode(new BPInternal(leftp, [[midkey, rightp]]));
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
            let [lkps, rkps] = span<[K, Ptr]>(([_, n]) => n !== leftnode, node.children);
            return new BPInternal(node.ptr, concat<[K, Ptr]>(lkps, cons<[K, Ptr]>(rkps[0], cons<[K, Ptr]>([k, rightnode], rkps))));
        }
    }
}
