#![allow(dead_code)]
use std::{fmt::Display, ops::Deref};

#[derive(Debug)]
/// Represents a node in a linked list.
///
/// # Fields
///
/// - `value`: The value stored in the node.
/// - `next`: An optional pointer to the next node in the list.
/// - `prev`: An optional pointer to the previous node in the list.
///
/// # Type Parameters
///
/// - `T`: The type of the value stored in the node.
struct Node<T: Sized> {
    value: T,
    next: Option<*mut Node<T>>,
    prev: Option<*mut Node<T>>,
}

impl<T: Sized> Drop for Node<T> {
    fn drop(&mut self) {}
}

impl<T: Sized> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// Represents a generic linked list.
///
/// The `List` struct is used to store a collection of elements of type `T` in a linked list format.
/// It maintains a reference to the head and tail nodes of the list.
///
/// # Type Parameters
///
/// - `T`: The type of elements stored in the list. (e.g., `i32`, `String`, etc.)
///
/// # Fields
///
/// - `head`: An optional raw pointer to the head node of the list.
/// - `tail`: An optional raw pointer to the tail node of the list.
///
/// # Safety
///
/// The `List` struct uses raw pointers to represent the head and tail nodes of the list.
/// It is important to ensure that these pointers are valid and properly managed to avoid
/// undefined behavior and memory safety issues.
///
#[derive(Debug, Default)]
pub struct List<T: Sized> {
    head: Option<*mut Node<T>>,
    tail: Option<*mut Node<T>>,
    len: usize,
}

#[macro_export]
macro_rules! list {
    ($($x:expr),*) => {{
        let mut list = List::new();
        $(list.insert_tail($x).unwrap();)*
        list
    }};
}

impl<T: Sized> Drop for List<T> {
    fn drop(&mut self) {
        let mut current = self.head;
        // Basicamente avanzo el cursor, dropeando todos los nodos, hasta que encuentro el None. (el final de la lista)
        while let Some(node) = current {
            current = unsafe {
                let next = (*node).next;
                drop(Box::from_raw(node));
                next
            }
        }
    }
}

impl<T: Sized> List<T> {
    /// Creates a new empty `List`.
    ///
    /// # Returns
    ///
    /// A new empty `List`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tp2_rs::List;
    /// let list: List<i32> = List::new();
    /// assert!(list.is_empty());
    /// ```
    ///
    pub const fn new() -> Self {
        List {
            len: 0,
            head: None,
            tail: None,
        }
    }
    /// Returns the number of elements in the list.
    ///
    /// # Returns
    ///
    /// The number of elements in the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// assert_eq!(list.len(), 0);
    /// list.insert_head(1).unwrap();
    /// assert_eq!(list.len(), 1);
    /// list.insert_head(2).unwrap();
    /// assert_eq!(list.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
    /// Returns `true` if the list is empty.
    ///
    /// # Returns
    ///
    /// `true` if the list is empty, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// assert!(list.is_empty());
    /// list.insert_head(1).unwrap();
    /// assert!(!list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Inserts a new element at the head of the list.
    /// The new element becomes the new head of the list.
    /// If the list is empty, the new element also becomes the tail of the list.
    /// The operation may fail if memory allocation for the new node fails. (e.g., out of memory, the operation is nightly only (Box::try_new))
    /// # Arguments
    /// - `value`: The value to insert into the list.
    /// # Returns
    /// `Ok(())` if the operation was successful, or an error message if the operation failed.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_head(1).unwrap();
    /// list.insert_head(2).unwrap();
    /// list.insert_head(3).unwrap();
    /// assert_eq!(list.peek_head(), Some(&3));
    /// ```
    pub fn insert_head(&mut self, value: T) -> Result<(), String> {
        match self.head {
            Some(node) => {
                let new_node = Box::into_raw(Box::new(Node {
                    value,
                    next: Some(node),
                    prev: None,
                }));
                unsafe {
                    (*node).prev = Some(new_node);
                }
                self.head = Some(new_node);
            }
            None => {
                self.head = Some(Box::into_raw(Box::new(Node {
                    value,
                    next: None,
                    prev: None,
                })));
                self.tail = self.head;
            }
        }
        self.len += 1;
        Ok(())
    }

    /// Inserts a new element at the tail of the list.
    /// The new element becomes the new tail of the list.
    /// If the list is empty, the new element also becomes the head of the list.
    /// The operation may fail if memory allocation for the new node fails. (e.g., out of memory, the operation is nightly only (Box::try_new))
    /// # Arguments
    /// - `value`: The value to insert into the list.
    /// # Returns
    /// `Ok(())` if the operation was successful, or an error message if the operation failed.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_tail(1).unwrap();
    /// list.insert_tail(2).unwrap();
    /// list.insert_tail(3).unwrap();
    /// assert_eq!(list.peek_tail(), Some(&3));
    /// ```
    pub fn insert_tail(&mut self, value: T) -> Result<(), String> {
        match self.tail {
            Some(node) => {
                let new_node = Box::into_raw(Box::new(Node {
                    value,
                    next: None,
                    prev: Some(node),
                }));
                unsafe {
                    (*node).next = Some(new_node);
                }
                self.tail = Some(new_node);
            }
            None => {
                self.tail = Some(Box::into_raw(Box::new(Node {
                    value,
                    next: None,
                    prev: None,
                })));
                self.head = self.tail;
            }
        }
        self.len += 1;
        Ok(())
    }

    /// Returns a reference to the value at the head of the list.
    /// # Returns
    /// A reference to the value at the head of the list, or `None` if the list is empty.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_head(1).unwrap();
    /// list.insert_head(2).unwrap();
    /// list.insert_head(3).unwrap();
    /// assert_eq!(list.peek_head(), Some(&3));
    /// ```
    pub fn peek_head(&self) -> Option<&T> {
        self.head.map(|node| unsafe { &(*node).value }) // Lo convierto en una referencia normal con .map() 😀
    }

    /// Returns a reference to the value at the tail of the list.
    /// # Returns
    /// A reference to the value at the tail of the list, or `None` if the list is empty.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_tail(1).unwrap();
    /// list.insert_tail(2).unwrap();
    /// list.insert_tail(3).unwrap();
    /// assert_eq!(list.peek_tail(), Some(&3));
    /// ```
    pub fn peek_tail(&self) -> Option<&T> {
        self.tail.map(|node| unsafe { &(*node).value }) // Lo convierto en una referencia normal con .map() 😀
    }

    /// Removes and returns the value at the head of the list.
    /// # Returns
    /// The value at the head of the list, or `None` if the list is empty.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_head(1).unwrap();
    /// list.insert_head(2).unwrap();
    /// list.insert_head(3).unwrap();
    /// assert_eq!(list.pop_head(), Some(3));
    /// assert_eq!(list.pop_head(), Some(2));
    /// assert_eq!(list.pop_head(), Some(1));
    /// assert_eq!(list.pop_head(), None);
    /// ```
    pub fn pop_head(&mut self) -> Option<T>
    where
        T: Clone,
    {
        if let Some(node) = self.head {
            let value = unsafe { (*node).value.clone() }; // tiene que ser clone, sino no me permite mover la referencia mientras la lista posea ese valor...
            self.head = unsafe { (*node).next };
            if let Some(next_node) = self.head {
                // Si el siguiente nodo es valido...
                unsafe {
                    (*next_node).prev = None;
                }
            } else {
                // Sino es valido, se vacio la lista 😀
                self.tail = None;
            }
            unsafe {
                drop(Box::from_raw(node)); // equivalente de hacer un free()
            }
            self.len -= 1;
            Some(value)
        } else {
            None
        }
    }

    /// Removes and returns the value at the tail of the list.
    /// # Returns
    /// The value at the tail of the list, or `None` if the list is empty.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_tail(1).unwrap();
    /// list.insert_tail(2).unwrap();
    /// list.insert_tail(3).unwrap();
    /// assert_eq!(list.pop_tail(), Some(3));
    /// assert_eq!(list.pop_tail(), Some(2));
    /// assert_eq!(list.pop_tail(), Some(1));
    /// assert_eq!(list.pop_tail(), None);
    /// ```
    pub fn pop_tail(&mut self) -> Option<T>
    where
        T: Clone,
    {
        if let Some(node) = self.tail {
            let value = unsafe { (*node).value.clone() };
            self.tail = unsafe { (*node).prev };
            if let Some(prev_node) = self.tail {
                unsafe {
                    (*prev_node).next = None;
                }
            } else {
                self.head = None;
            }
            unsafe {
                drop(Box::from_raw(node));
            }
            self.len -= 1;
            Some(value)
        } else {
            None
        }
    }

    /// Returns an iterator over the elements of the list.
    /// The iterator yields elements in the order they appear in the list.
    /// # Returns
    /// An iterator over the elements of the list.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_tail(1).unwrap();
    /// list.insert_tail(2).unwrap();
    /// list.insert_tail(3).unwrap();
    /// for (n, value) in (1..=3).zip(list.iter()) {
    ///    assert_eq!(n, *value);
    /// }  
    /// ```
    pub fn iter(&self) -> ListIterator<T> {
        ListIterator {
            current: self.head.map(|node| node as *const Node<T>),
            marker: std::marker::PhantomData,
        }
    }

    /// Returns an iterator that allows modifying the elements of the list.
    /// The iterator yields mutable references to the elements in the order they appear in the list.
    /// # Returns
    /// An iterator that allows modifying the elements of the list.
    /// # Examples
    /// ```
    /// use tp2_rs::List;
    /// let mut list = List::new();
    /// list.insert_tail(1).unwrap();
    /// list.insert_tail(2).unwrap();
    /// list.insert_tail(3).unwrap();
    /// for value in list.iter_mut() {
    ///   *value *= 2;
    /// }
    /// for (n, value) in (1..=3).zip(list.iter()) {
    ///   assert_eq!(n * 2, *value);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> ListIteratorMut<T> {
        let head = self.head; // Option es Copy, asi que no hay problema en hacer esto.
        ListIteratorMut {
            list: self,
            current: head,
            marker: std::marker::PhantomData,
        }
    }
}

impl<T: Sized + Display + Copy> Display for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut current = &self.head;
        while let Some(node) = current {
            // ! Medio desagradable la cantidad de dereferencias, pero es lo que hay.
            write!(f, "{} <-> ", unsafe { (*(*node)).value })?;
            current = unsafe { &(*(*node)).next };
        }
        write!(f, "None")
    }
}

/// # Nota
/// El iterador de la lista es un iterador simple, que no permite modificar la lista mientras se itera.
/// Para modificar la lista mientras se itera, se debe utilizar el iterador mutable.
///
/// En particular necesita un lifetime asociado al lifetime del generico T, sino no se podria saber si el iterador esta iterando por referencias validas.
/// La gracia es forzar esto en tiempo de compilacion en vez de usando RefCell<T>, u otros smart pointers.
pub struct ListIterator<'a, T: Sized> {
    current: Option<*const Node<T>>,
    marker: std::marker::PhantomData<&'a T>,
}

/// # Nota
/// El iterador mutable de la lista permite modificar la lista mientras se itera.
/// La misma explicacion que el iterador simple, pero en este caso se necesita una lifetime hacia una referencia exclusiva a T.
pub struct ListIteratorMut<'a, T: Sized> {
    list: &'a mut List<T>,
    current: Option<*mut Node<T>>,
    marker: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T: Sized> Iterator for ListIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.map(|node| {
            //? Se de antemano que el puntero es valido (garantizado por Box<>), por lo que puedo hacer un unsafe dereference.
            let node = unsafe { &*node };
            //? `next` es *mut porque next() toma una referencia exclusiva al iterador. self.current en cambio es *const, asi que tengo que hacer la conversion in place para que sea valida la siguiente "referenciacion".
            self.current = node.next.map(|next| next as *const Node<T>);
            &node.value
        })
    }
}

// Para poder usarlo directmente en un for loop y no llamar a .iter() explicitamente.
impl<'a, T: Sized> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIterator<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Sized> DoubleEndedIterator for ListIterator<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.current.map(|node| {
            let node = unsafe { &*node };
            self.current = node.prev.map(|prev| prev as *const Node<T>);
            &node.value
        })
    }
}

impl<'a, T: Sized> Iterator for ListIteratorMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.take().map(|node| {
            let node = unsafe { &mut *node };
            self.current = node.next;
            &mut node.value
        })
    }
}

impl<'a, T: Sized> DoubleEndedIterator for ListIteratorMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.current.take().map(|node| {
            let node = unsafe { &mut *node };
            self.current = node.prev;
            &mut node.value
        })
    }
}

impl<'a, T: Sized> ListIterator<'a, T> {
    /// Returns a reference to the value at the current position of the iterator. (ya existe peekable, pero bueno, lo hago yo por si las dudas...)
    pub fn peek(&self) -> Option<&T> {
        self.current.map(|node| {
            let node = unsafe { &*node };
            &node.value
        })
    }
    /// Returns `true` if the iterator is at the end of the list.
    pub fn at_end(&self) -> bool {
        self.current
            .map(|node| unsafe { (*node).next.is_none() })
            .unwrap_or(true) // Si es None, current es None, por lo que esta en el final...
    }
    /// Returns `true` if the iterator is at the beginning of the list.
    pub fn at_beggining(&self) -> bool {
        self.current
            .map(|node| unsafe { (*node).prev.is_none() })
            .unwrap_or(true) // Si es None, significa que tengo la lista vacia, caso que esta en el final y en el principio.
    }
}

impl<'a, T: Sized> ListIteratorMut<'a, T> {
    /// Returns a reference to the value at the current position of the iterator.
    pub fn peek(&self) -> Option<&T> {
        self.current.as_ref().map(|node| {
            let node = unsafe { &**node };
            &node.value
        })
    }
    /// Returns `true` if the iterator is at the end of the list.
    pub fn at_end(&self) -> bool {
        self.current
            .as_ref()
            .map(|node| {
                let node = unsafe { &**node }; // Se que el puntero es valido...
                node.next.is_none()
            })
            .unwrap_or(true)
    }
    /// Returns `true` if the iterator is at the beginning of the list.
    pub fn at_beggining(&self) -> bool {
        self.current
            .as_ref()
            .map(|node| {
                let node = unsafe { &**node };
                node.prev.is_none()
            })
            .unwrap_or(true)
    }
    /// Inserts a new element after the current position of the iterator.
    ///
    /// Example:
    /// ```
    /// use tp2_rs::{List, list};
    ///
    /// let mut list = list!(1, 2, 3, 4, 5, 7);
    ///
    /// {
    ///     let mut list_iter = list.iter_mut();
    ///     list_iter.insert_after(10);
    ///     println!("list: {}", list);
    /// }
    /// assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec![1, 10, 2, 3, 4, 5, 7]);
    /// ```
    pub fn insert_after(&mut self, value: T) {
        // El nodo actual es valido
        if let Some(node) = self.current {
            // Creo espacio para el nuevo nodo
            let new_node = Box::into_raw(Box::new(Node {
                value,
                next: unsafe { (*node).next },
                prev: Some(node),
            }));
            // Si no estoy en el final de la lista, tengo que actualizar el nodo siguiente.
            if let Some(next_node) = unsafe { (*node).next } {
                unsafe {
                    (*next_node).prev = Some(new_node);
                }
            } else {
                // Si estoy en el final de la lista, actualizo la cola.
                self.list.tail = Some(new_node);
            }
            // Actualizo el nodo actual. (el que va a estar detras del nuevo nodo)
            unsafe {
                (*node).next = Some(new_node);
            }
        } else {
            // Si el nodo actual no es valido, inserto al principio de la lista.
            self.list.insert_head(value).unwrap();
        }
        self.list.len += 1;
    }

    /// Inserts a new element before the current position of the iterator.
    ///
    /// Example:
    /// ```
    /// use tp2_rs::{List, list};
    ///
    /// let mut list = list!(1, 2, 3, 4, 5, 7);
    ///     
    /// {
    ///     let mut list_iter = list.iter_mut();
    ///     list_iter.next();
    ///     list_iter.insert_before(23);
    ///     list_iter.next();
    ///     list_iter.insert_before(10);
    /// }
    /// assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec![1, 23, 2, 10, 3, 4, 5, 7]);
    /// ```
    pub fn insert_before(&mut self, value: T) {
        // El nodo actual es valido
        if let Some(node) = self.current {
            // Creo espacio para el nuevo nodo
            let new_node = Box::into_raw(Box::new(Node {
                value,
                next: Some(node),
                prev: unsafe { (*node).prev },
            }));
            // Si no estoy en el principio de la lista, tengo que actualizar el nodo anterior.
            if let Some(prev_node) = unsafe { (*node).prev } {
                unsafe {
                    (*prev_node).next = Some(new_node);
                }
            } else {
                // Si estoy en el principio de la lista, actualizo la cabeza.
                self.list.head = Some(new_node);
            }
            // Actualizo el nodo actual. (el que va a estar delante el nuevo nodo)
            unsafe {
                (*node).prev = Some(new_node);
            }
        } else {
            // Si el nodo actual no es valido, inserto al final de la lista.
            self.list.insert_tail(value).unwrap();
        }
        self.list.len += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_list() {
        let mut list = List::new();
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        list.insert_head(1).unwrap();
        assert_eq!(list.len(), 1);
        assert!(!list.is_empty());
        list.insert_head(2).unwrap();
        assert_eq!(list.len(), 2);
        assert!(!list.is_empty());
    }
    #[test]
    fn test_list_iter() {
        let mut list = List::new();
        list.insert_head(1).unwrap();
        list.insert_head(2).unwrap();
        list.insert_head(3).unwrap();
        list.insert_head(4).unwrap();
        list.insert_head(5).unwrap();
        assert!(list.len() == 5);
        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_list_iter_back() {
        let mut list = List::new();
        list.insert_head(1).unwrap();
        list.insert_head(2).unwrap();
        list.insert_head(3).unwrap();
        list.insert_head(4).unwrap();
        list.insert_head(5).unwrap();
        assert!(list.len() == 5);
        let mut iter = list.iter();
        // El comportamiento es medio extraño, pero basicamente yieldea el valor actual y luego se mueve al siguiente.
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.peek(), Some(&1));
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.next_back(), Some(&5));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_list_iter_tail() {
        let mut list = List::new();
        list.insert_tail(1).unwrap();
        list.insert_tail(2).unwrap();
        list.insert_tail(3).unwrap();
        list.insert_tail(4).unwrap();
        list.insert_tail(5).unwrap();
        assert!(list.len() == 5);
        for value in list.iter() {
            println!("{}", value);
        }
    }

    #[test]
    fn test_list_iter_peek() {
        let mut list = List::new();
        list.insert_tail(1).unwrap();
        list.insert_tail(2).unwrap();
        list.insert_tail(3).unwrap();
        list.insert_tail(4).unwrap();
        list.insert_tail(5).unwrap();
        assert!(list.len() == 5);
        assert_eq!(list.peek_head(), Some(&1));
        assert_eq!(list.peek_tail(), Some(&5));
    }

    #[test]
    fn test_list_pop() {
        let mut list = List::new();
        list.insert_tail(1).unwrap();
        list.insert_tail(2).unwrap();
        list.insert_tail(3).unwrap();
        list.insert_tail(4).unwrap();
        list.insert_tail(5).unwrap();
        assert!(list.len() == 5);
        assert_eq!(list.pop_head(), Some(1));
        assert_eq!(list.pop_head(), Some(2));
        assert_eq!(list.pop_head(), Some(3));
        assert_eq!(list.pop_head(), Some(4));
        assert_eq!(list.pop_head(), Some(5));
        assert_eq!(list.pop_head(), None);
        assert!(list.is_empty());
    }

    #[test]
    fn test_list_pop_tail() {
        let mut list = List::new();
        list.insert_tail(1).unwrap();
        list.insert_tail(2).unwrap();
        list.insert_tail(3).unwrap();
        list.insert_tail(4).unwrap();
        list.insert_tail(5).unwrap();
        assert!(list.len() == 5);
        assert_eq!(list.pop_tail(), Some(5));
        assert_eq!(list.pop_tail(), Some(4));
        assert_eq!(list.pop_tail(), Some(3));
        assert_eq!(list.pop_tail(), Some(2));
        assert_eq!(list.pop_tail(), Some(1));
        assert_eq!(list.pop_tail(), None);
        assert!(list.is_empty());
    }

    #[test]
    fn test_list_pop_tail_head() {
        let mut list = List::new();
        list.insert_tail(1).unwrap();
        list.insert_tail(2).unwrap();
        list.insert_tail(3).unwrap();
        list.insert_tail(4).unwrap();
        list.insert_tail(5).unwrap();
        assert!(list.len() == 5);
        assert_eq!(list.pop_tail(), Some(5));
        assert_eq!(list.pop_head(), Some(1));
        assert_eq!(list.pop_tail(), Some(4));
        assert_eq!(list.pop_head(), Some(2));
        assert_eq!(list.pop_tail(), Some(3));
        assert_eq!(list.pop_head(), None);
        assert!(list.is_empty());
    }
    #[test]
    fn test_iter_insert_after() {
        let mut list = list!(1, 2, 3, 4, 5, 7);
        {
            let mut list_iter = list.iter_mut();
            list_iter.insert_after(10);
        }
        assert_eq!(
            list.iter().cloned().collect::<Vec<_>>(),
            vec![1, 10, 2, 3, 4, 5, 7]
        );
    }
    #[test]
    fn test_iter_insert_before() {
        let mut list = list!(1, 2, 3, 4, 5, 7);
        {
            let mut list_iter = list.iter_mut();
            list_iter.next();
            list_iter.insert_before(23);
            list_iter.next();
            list_iter.insert_before(10);
        }
        assert_eq!(
            list.iter().cloned().collect::<Vec<_>>(),
            vec![1, 23, 2, 10, 3, 4, 5, 7]
        );
    }

    #[test]
    fn test_list_insert_before_and_after() {
        let mut list = list!(1, 2, 3, 4, 5, 7);
        {
            let mut list_iter = list.iter_mut();
            list_iter.next();
            list_iter.insert_before(23);
            list_iter.next();
            list_iter.insert_before(10);
            list_iter.next();
            list_iter.insert_after(10);
        }
        assert_eq!(
            list.iter().cloned().collect::<Vec<_>>(),
            vec![1, 23, 2, 10, 3, 4, 10, 5, 7]
        );
    }
}
