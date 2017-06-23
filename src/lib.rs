
#[derive(Debug)]
struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
    balance: u8,
}

#[derive(Debug)]
struct Tree<T: Ord> {
    root: Option<Box<Node<T>>>,
}


struct TreeIter<'a, T: 'a + Ord> {
    tree: &'a Tree<T>,
    queue: Vec<&'a T>,
}

impl<'a, T: Ord> TreeIter<'a, T> {
    fn new(tree: &'a Tree<T>) -> TreeIter<T> {
        TreeIter { tree: &tree, queue: Vec::new() }
    }
}

impl<'a, T: Ord> Iterator for TreeIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        match self.tree.root {
            None => None,
            Some(ref node) => Some(&node.value),
        }
    }
}

impl<T: Ord> Tree<T> {
    fn new() -> Tree<T> {
        Tree { root: None }
    }
    
    fn insert(&mut self, val: T) {
    }

    fn iter(&self) -> TreeIter<T>{
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
        assert_eq!(123, *t.iter().next().unwrap());
    }
}
