//! entry module
use crate::Node;

/// An entry in a tree. This is a lower-level version of the `map::Entry` API.
pub enum Entry<'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, V>),
}

impl<'a, V: 'a> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Entry<'a, V> {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

/// A view into an occupied entry in a tree.
/// It is part of the `Entry` enum.
pub struct OccupiedEntry<'a, V: 'a> {
    pub(crate) node: &'a mut Node<V>,
}

impl<'a, V: 'a> OccupiedEntry<'a, V> {
    /// Gets a reference to the value in the entry
    pub fn get(&self) -> &V {
        // An occupied entry always has a value.
        self.node.value().unwrap()
    }

    /// Gets a mutable reference to the value in the entry
    pub fn get_mut(&mut self) -> &mut V {
        self.node.value_mut().unwrap()
    }

    /// Converts the entry into a mutable reference to its value
    pub fn into_mut(self) -> &'a mut V {
        self.node.value_mut().unwrap()
    }

    /// Replaces the value in the entry with the given one and returns the old value
    pub fn insert(&mut self, value: V) -> V {
        core::mem::replace(self.get_mut(), value)
    }
}

/// A view into a vacant entry in a tree.
/// It is part of the `Entry` enum.
pub struct VacantEntry<'a, V: 'a> {
    pub(crate) node: &'a mut Node<V>,
}

impl<'a, V: 'a> VacantEntry<'a, V> {
    /// Sets the value for the entry and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        self.node.set_value(value);
        self.node.value_mut().unwrap()
    }
}
