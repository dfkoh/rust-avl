use std::rc::{Rc, Weak};
use std::cell::RefCell;


#[derive(Debug)]
struct Node<T: Ord> {
    value: Rc<T>,
    left: Option<NodePtr<T>>,
    right: Option<NodePtr<T>>,
    balance: u8,
}

type NodePtr<T> = Rc<RefCell<Node<T>>>;

impl<T: Ord> Node<T> {
    fn new(val: T) -> Node<T> {
        Node { value: Rc::new(val), left: None, right: None, balance: 0 }
    }

    fn add_child(&mut self, val: T) {
        let child = if val < *self.value {
            &mut self.left  
        } else {
            &mut self.right
        };

        match child {
            &mut None => { *child = Some(Rc::new(RefCell::new(Node::new(val)))) },
            &mut Some(ref node) => { node.borrow_mut().add_child(val); },
        }
    }
}

#[derive(Debug)]
pub struct Tree<T: Ord> {
    root: Option<NodePtr<T>>,
}


pub struct TreeIter<T: Ord> {
    queue: Vec<Weak<RefCell<Node<T>>>>,
}

impl<T: Ord> TreeIter<T> {
    fn add_subtree(&mut self, root: Option<NodePtr<T>>) {
        let mut node_opt = root;
        while node_opt.is_some() {
            let node = node_opt.unwrap();
            self.queue.push(Rc::downgrade(&node));
            node_opt = node.borrow().left.clone();
        }
    }

    fn new(tree: &Tree<T>) -> TreeIter<T> {
        let mut iter = TreeIter { queue: Vec::new() };
        iter.add_subtree(tree.root.clone());
        iter
    }
}

impl<T: Ord> Iterator for TreeIter<T> {
    type Item = Rc<T>;
    fn next(&mut self) -> Option<Self::Item> {
        let node_weak = self.queue.pop();
        if node_weak.is_none() { return None; }

        match node_weak.unwrap().upgrade() {
            None => None,
            Some(node) => {
                self.add_subtree(node.borrow().right.clone());
                Some(node.borrow().value.clone())
            }
        }
    }
}

impl<T: Ord> Tree<T> {
    pub fn new() -> Tree<T> {
        Tree { root: None }
    }
    
    pub fn insert(&mut self, val: T) {
        if let Some(ref node) = self.root {
            node.borrow_mut().add_child(val);
        } else {
            self.root = Some(Rc::new(RefCell::new(Node::new(val))));
        }
    }

    pub fn iter(&self) -> TreeIter<T>{
        TreeIter::new(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iter_basic() {
        let t: Tree<u32> = Tree::new();
        assert_eq!(None, t.iter().next());
    }

    #[test]
    fn insert_basic() {
        let mut t = Tree::new();
        t.insert(123);
        assert_eq!(123, *t.iter().next().expect("iter ended early"));
    }
    
    #[test]
    fn insert_two() {
        let mut t = Tree::new();
        t.insert(123);
        t.insert(345);
        let mut itr = t.iter();
        println!("{:?}", t);
        assert_eq!(123, *itr.next().expect("iter ended early"));
        assert_eq!(345, *itr.next().expect("iter ended early"));
    }

}
