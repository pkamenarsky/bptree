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

function append<A>(as: A[], a: A): A[] {
    return [];
}

function tail<A>(as: A[]): A[] {
    return [];
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
    children: [V, Ptr][];

    constructor(ptr: Ptr, children: [V, Ptr][]) {
        this.ptr = ptr;
        this.children = children;
    }
}

// type BPNode<K, V> = BPInternal<V> | BPLeaf<K, V>;

class BPTree<K, V> {
    root: Ptr;
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

function insertLeaf<K, V>(tree: BPTree<K, V>, node: Ptr, path: Ptr[], k: K, v: V, kvs: [K, V][], mptr: Ptr) {
    let sz = tree.backend.getSize();

    if (kvs.length + 1 <= sz) {
        tree.backend.setNode(node, new BPLeaf(insert<[K, V]>([k, v], kvs), mptr));
    }
    else {
        let half = undefined;
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
            lefts_ = append<[K, V]>(lefts, [rk, rv]);
            rights_ = insert<[K, V]>([k, v], rights);
        }

        midk = rights_[0][0];

        let rightnode = tree.backend.createNode(new BPLeaf(rights_, mptr));
        tree.backend.setNode(leftnode, new BPLeaf(lefts_, rightnode));

        if (path.length == 0) {
            tree.backend.createRoot(new BPInternal(leftnode, [[midk, rightnode]]));
        }
        else {
            insertLink(path[0], tail(path), leftnode, midk, rightnode);
        }
    }
}

function insertLink<K, V>(node: Ptr, path: Ptr[], leftnode: Ptr, midk: K, rightnode: Ptr) {
}
