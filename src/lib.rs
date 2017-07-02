#![feature(test)]

extern crate test;
extern crate rand;

use std::cmp;

#[derive(Debug)]
struct Node<K: Ord, V: PartialEq> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
    balance: i8,
}

impl<K: Ord, V: PartialEq> PartialEq for Node<K, V> {
    fn eq(&self, other: &Node<K, V>) -> bool {
        return self.key == other.key && self.value == other.value;
    }
}
impl<K: Ord, V: Eq> Eq for Node<K, V> {}


impl<K: Ord, V: PartialEq> Node<K, V> {
    fn new(key: K, val: V) -> Node<K, V> {
        Node { key: key, value: val, left: None, right: None, balance: 0 }
    }

    // Return the new root ptr, and if the tree got taller
    fn insert(mut node_ptr: Option<Box<Node<K, V>>>, 
                 key: K, val: V) -> (Option<Box<Node<K, V>>>, bool) 
    {
        if node_ptr.is_none() {
            return (Some(Box::new(Node::new(key, val))), true);
        }

        let mut grew = false;
        let mut change = 0;
        {
            let node = node_ptr.as_mut().unwrap();
            if key == node.key {
                node.value = val;
            }
            else if key < node.key {
                let (lnode, lgrew) = Node::insert(node.left.take(), key, val);
                grew = lgrew;
                node.left = lnode;
                change = -1;
            } 
            else {
                let (rnode, rgrew) = Node::insert(node.right.take(), key, val);
                grew = rgrew;
                node.right = rnode;
                change = 1;
            }
        }

        if !grew {
            // No need to balance if the sub-tree didn't get taller
            //assert_eq!(Ok(()), node_ptr.as_ref().unwrap()._check_invariants());
            (node_ptr, false)
        } else {
            let (new_node, grew) = Node::balance(node_ptr.unwrap(), change);
            //assert_eq!(Ok(()), new_node._check_invariants());
            (Some(new_node), grew)
        }
    }

    fn balance(mut node: Box<Node<K, V>>, change: i8)
        -> (Box<Node<K, V>>, bool) 
    {
        // Record the old balance so we can tell if we get taller
        let old_balance = node.balance;
        node.balance += change;

        // Balance a lean too far to the right
        if node.balance > 1 { 
            assert!(node.right.is_some());
            if node.right.as_ref().unwrap().balance < 0 {
                node.right = Some(
                    Node::rotate_right(node.right.take().unwrap()));
            } 
            node = Node::rotate_left(node);
        } 
        // Balance a lean too far to the left
        else if node.balance < -1 { 
            assert!(node.left.is_some());
            if node.left.as_ref().unwrap().balance > 0 {
                node.left = Some(
                    Node::rotate_left(node.left.take().unwrap()));
            } 
            node = Node::rotate_right(node);
        } 

        let grew = node.balance.abs() > old_balance.abs();
        (node, grew)
    }
    // Rotation Documentation
    //
    //    Left         Right
    //  
    //       y           x
    //      / \         / \
    //     x   C  <->  A   y
    //    / \             / \
    //   A   B           B   C
    //
    // Balance formulas:
    //
    // x_L = B-A
    // y_L = C-(B+1) if x_L > 0
    //       C-(A+1) if x_L <= 0
    //
    // x_R = (C+1)-A if y_R > 0
    //     = (B+1)-A if y_R <= 0
    // y_R = C-B
    //
    //
    // Right rotate transform:
    //
    // y_R = y_L + 1       if x_L > 0
    //     = y_L - x_L + 1 if x_L <= 0
    // x_R = x_L + y_R + 1 if y_R > 0
    //     = x_L + 1       if y_R <= 0
    //
    // Left rotate transform:
    //
    // x_L = x_R - y_R - 1 if y_R > 0
    //     = x_R - 1       if y_R <= 0
    // y_L = y_R - 1       if x_L > 0
    //     = y_R + x_L - 1 if x_L => 0
    //
    #[allow(non_snake_case)]
    fn rotate_right(mut root: Box<Node<K, V>>) -> Box<Node<K, V>> {
        assert!(root.left.is_some());
        let mut new_root = root.left.take().unwrap();

        let y_L = root.balance;
        let x_L = new_root.balance;
        let y_R = if x_L > 0 { y_L + 1 } else { y_L - x_L + 1 };
        let x_R = if y_R > 0 { x_L + y_R + 1 } else { x_L + 1 };
        root.balance = y_R;
        new_root.balance = x_R;

        root.left = new_root.right.take();
        new_root.right = Some(root);
        new_root
    }
    #[allow(non_snake_case)]
    fn rotate_left(mut root: Box<Node<K, V>>) -> Box<Node<K, V>> {
        assert!(root.right.is_some());
        let mut new_root = root.right.take().unwrap();

        let x_R = root.balance;
        let y_R = new_root.balance;
        let x_L = if y_R > 0 { x_R - y_R - 1 } else { x_R - 1 };
        let y_L = if x_L > 0 { y_R - 1 } else { y_R + x_L - 1 };
        root.balance = x_L;
        new_root.balance = y_L;

        root.right = new_root.left.take();
        new_root.left = Some(root);
        new_root
    }

    fn _check_invariants(&self) -> Result<(), &'static str> {
        let check = |node: &Self| {
            if node.balance.abs() > 1 {
                return Err("Node out of balance");
            }
            let left_height = node.left.as_ref()
                .map_or(0, |n| n.height()) as isize;
            let right_height = node.right.as_ref()
                .map_or(0, |n| n.height()) as isize;

            if (right_height - left_height).abs() > 1 {
                return Err("Node out of balance (height check)");
            }
            if node.balance != (right_height - left_height) as i8 {
                return Err("Balance doesn't match height");
            }
            Ok(())
        };

        self.fold(Ok(()), |b, n| { 
            match b {
                Ok(()) => check(&n),
                Err(_) => b,
            }
        })
    }

    fn fold<B, F>(&self, init: B, f: F) -> B 
        where F: Fn(B, &Self) -> B, 
    {
        let mut accum = init;
        if let Some(ref node) = self.left {
            accum = f(accum, node.as_ref());
        }
        if let Some(ref node) = self.right {
            accum = f(accum, node.as_ref());
        }

        accum
    }
    fn len(&self) -> usize {
        self.fold(1, |b, n| { b + n.len() })
    }
    fn height(&self) -> usize {
        self.fold(1, |b, n| { cmp::max(b, n.height() + 1) })
    }
    fn get(&self, key: K) -> Option<&V> {
        if key == self.key {
            return Some(&self.value);
        }

        if key < self.key && self.left.is_some() {
            return self.left.as_ref().and_then(|n| n.get(key));
        }

        if key > self.key && self.right.is_some() {
            return self.right.as_ref().and_then(|n| n.get(key));
        }

        return None;
    }

}

#[derive(Debug)]
pub struct Tree<K: Ord, V: PartialEq> {
    root: Option<Box<Node<K, V>>>,
}

macro_rules! tree_fn {
    ($func_name:ident($($arg:ident: $arg_type:ty),*) -> $return_type:ty, $default:expr) => {
        pub fn $func_name(&self, $($arg: $arg_type),*) -> $return_type {
            if let Some(ref node) = self.root {
                node.$func_name($($arg),*)
            } else {
                $default
            }
        }
    }
}

impl<K: Ord, V: PartialEq> Tree<K, V> {
    pub fn new() -> Tree<K, V> {
        Tree { root: None }
    }
    
    pub fn insert(&mut self, key: K, val: V) {
        self.root = Node::insert(self.root.take(), key, val).0;
    }

    pub fn iter<'a>(&'a self) -> TreeIter<'a, K, V> {
        TreeIter { 
            curr: self.root.as_ref(), 
            curr_branch: Branch::Left, 
            stack: Vec::new() 
        }
    }

    tree_fn!(len() -> usize, 0);
    tree_fn!(height() -> usize, 0);
    tree_fn!(get(key: K) -> Option<&V>, None);
}


// Iterative implementation of tree walk
//
// Tree walk recursive function would look like this:
// (Left)  recurse into left subtree
// (Yield) yield self
// (Right) recurse into right subtree
// (Done)  return
//
#[derive(Debug, Clone, Copy)]
enum Branch {
    Left,
    Yield,
    Right,
    Done
}

#[derive(Debug)]
pub struct TreeIter<'a, K: Ord + 'a, V: PartialEq + 'a>{
    curr: Option<&'a Box<Node<K, V>>>,
    curr_branch: Branch,
    stack: Vec<(&'a Box<Node<K, V>>, Branch)>,
}

impl<'a, K: Ord, V: PartialEq> Iterator for TreeIter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop { match self.curr_branch {
            Branch::Left => {
                match self.curr {
                    None => {
                        if let Some((new_curr, new_branch)) = self.stack.pop() {
                            self.curr = Some(new_curr);
                            self.curr_branch = new_branch;
                        } else {
                            return None;
                        }
                    },
                    Some(node) => {
                        self.curr = node.left.as_ref();
                        self.curr_branch = Branch::Left;

                        self.stack.push((node, Branch::Yield));
                    }
                }
            },
            Branch::Yield => {
                assert!(self.curr.is_some());
                self.curr_branch = Branch::Right;
                let n = self.curr.unwrap();
                return Some((&n.key, &n.value));
            }
            Branch::Right => {
                assert!(self.curr.is_some());
                let node = self.curr.unwrap();
                self.curr = node.right.as_ref();
                self.curr_branch = Branch::Left;

                self.stack.push((node, Branch::Done));
            }
            Branch::Done => {
                if let Some((new_curr, new_branch)) = self.stack.pop() {
                    self.curr = Some(new_curr);
                    self.curr_branch = new_branch;
                } else {
                    return None;
                }
            }
        }}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use test::Bencher;

    mod node {
        use super::Node;

        fn build_tree() -> Node<char, u32> {
            let mut n = Some(Box::new(Node::new('b', 1)));
            n = Node::insert(n, 'a', 2).0;
            n = Node::insert(n, 'd', 3).0;
            n = Node::insert(n, 'c', 4).0;
            n = Node::insert(n, 'e', 5).0;
            *n.unwrap()
        }

        #[test]
        fn height() {
            let n = build_tree();
            let m = n.right.as_ref().unwrap();
            let k = n.left.as_ref().unwrap();
            assert_eq!(3, n.height());
            assert_eq!(2, m.height());
            assert_eq!(1, k.height());
        }

        #[test]
        fn balance() {
            let n = build_tree();
            let m = n.right.as_ref().unwrap();
            let k = n.left.as_ref().unwrap();
            let delta: i8 = (m.height() - k.height()) as i8;
            assert_eq!(n.balance, delta);
        }

    }

    mod tree {
        use super::Tree;
        #[test]
        fn len_basic() {
            let t: Tree<&str, u32> = Tree::new();
            assert_eq!(0, t.len());
        }

        #[test]
        fn insert_basic() {
            let mut t = Tree::new();
            t.insert("hi", 123);
            t.insert("woo", 123);
            t.insert("moo", 123);
            assert_eq!(3, t.len());
        }

        #[test]
        fn iter_basic() {
            let mut t = Tree::new();
            t.insert("hi", 123);
            t.insert("woo", 123);
            t.insert("moo", 123);
            {
                let mut iter = t.iter();
                assert_eq!("hi", *iter.next().unwrap().0);
                assert_eq!("moo", *iter.next().unwrap().0);
                assert_eq!("woo", *iter.next().unwrap().0);
                assert_eq!(None, iter.next());
            }
            t.insert("check borrow", 123);
        }
        
        #[test]
        fn get_basic() {
            let mut t = Tree::new();
            t.insert("hi", 123);
            t.insert("woo", 124);
            t.insert("moo", 125);

            assert_eq!(125, *t.get("moo").expect("get failed"));
        }

        #[test]
        fn insert_replace() {
            let mut t = Tree::new();
            t.insert("hi", 123);
            t.insert("hi", 234);
            assert_eq!(1, t.len());
            assert_eq!(234, *t.get("hi").expect("get failed"));
        }
    }

    #[bench]
    fn bench_tree_get_rand(b: &mut Bencher) {
        let mut rng = rand::thread_rng();
        let mut t: Tree<u32, u32> = Tree::new();
        for x in 1..1000000 {
            t.insert(rng.gen(), x);
        }
        println!("Tree height: {}", t.height());
        b.iter(|| {
            let mut out: u32 = 0;
            for _ in 1..1000 {
                let k = t.get(rng.gen());
                if k.is_some() {
                    out ^= *k.unwrap();
                }
            }
            out
        });
    }

    #[bench]
    fn bench_tree_inorder_insert(b: &mut Bencher) {
        b.iter(|| {
            let mut t: Tree<u32, ()> = test::black_box(Tree::new());
            for x in 1..1000 {
                t.insert(x, ());
            }
        });
    }

    #[bench]
    fn bench_tree_rand_insert(b: &mut Bencher) {
        let mut rng = rand::thread_rng();
        b.iter(|| {
            let mut t: Tree<u32, ()> = test::black_box(Tree::new());
            for _ in 1..1000 {
                t.insert(rng.gen(), ());
            }
        });
    }

}
