use std::rc::{Rc, Weak};
use std::cell::RefCell;
use std::cmp;

#[derive(Debug)]
struct Node<K: Ord, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
    balance: i8,
}

impl<K: Ord, V: Eq> PartialEq for Node<K, V> {
    fn eq(&self, other: &Node<K, V>) -> bool {
        return self.key == other.key && self.value == other.value;
    }
}
impl<K: Ord, V: Eq> Eq for Node<K, V> {}


impl<K: Ord, V> Node<K, V> {
    fn new(key: K, val: V) -> Node<K, V> {
        Node { key: key, value: val, left: None, right: None, balance: 0 }
    }

    // Returns whether or not this tree got taller
    fn add_child(&mut self, key: K, val: V) -> bool {
        let mut grew_left = false;
        let mut grew_right = false;
        if key < self.key {
            grew_left = Node::insert(&mut self.left, key, val);
        } else {
            grew_right = Node::insert(&mut self.right, key, val);
        }

        if grew_left {
            self.balance -= 1;
            return self.balance < 0;
        } 
        else if grew_right {
            self.balance += 1;
            return self.balance > 0;
        }
        false
    }

    // Returns whether or not the node got taller
    fn insert(node: &mut Option<Box<Node<K, V>>>, key: K, val: V) -> bool {
        if node.is_none() {
            *node = Some(Box::new(Node::new(key, val)));
            true
        } else {
            node.as_mut().unwrap().add_child(key, val)
        }
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

    fn find(&self, key: K) -> Option<&V> {
        if key == self.key {
            return Some(&self.value);
        }

        if key < self.key && self.left.is_some() {
            return self.left.as_ref().and_then(|n| n.find(key));
        }

        if key > self.key && self.right.is_some() {
            return self.right.as_ref().and_then(|n| n.find(key));
        }

        return None;
    }
}

#[derive(Debug)]
pub struct Tree<K: Ord, V> {
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

impl<K: Ord, V> Tree<K, V> {
    pub fn new() -> Tree<K, V> {
        Tree { root: None }
    }
    
    pub fn insert(&mut self, key: K, val: V) {
        Node::insert(&mut self.root, key, val);
    }

    tree_fn!(len() -> usize, 0);
    tree_fn!(find(key: K) -> Option<&V>, None);

    //pub fn find(&self, key: K) -> Option<&V> {
    //    None
    //}
}

#[cfg(test)]
mod tests {
    use super::*;

    mod node {
        use super::Node;

        fn build_tree() -> Node<char, u32> {
            let mut n = Node::new('b', 1);
            n.add_child('a', 2);
            n.add_child('d', 3);
            n.add_child('c', 4);
            n.add_child('e', 5);
            n
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
        fn find_basic() {
            let mut t = Tree::new();
            t.insert("hi", 123);
            t.insert("woo", 124);
            t.insert("moo", 125);

            assert_eq!(125, *t.find("moo").expect("find failed"));
        }
    }

}
