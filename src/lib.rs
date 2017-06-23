
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
    curr_node: Option<&'a Node<T>>,
}

impl<'a, T: Ord> TreeIter<'a, T> {
    fn new(tree: &'a Tree<T>) -> TreeIter<T> {
        TreeIter { tree: &tree, curr_node: None }
    }
}

impl<'a, T: Ord> Iterator for TreeIter<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        None
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
    fn insert_basic() {
        let mut t = Tree::new();
        t.insert(123);
        assert_eq!(123, t.iter().next().unwrap()) 
    }
}
