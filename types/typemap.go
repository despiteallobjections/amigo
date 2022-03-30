// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package typeutil defines various utilities for types, such as Map,
// a mapping from types.Type to interface{} values.
package types // import "github.com/mdempsky/amigo/typeutil"

import (
	"bytes"
	"fmt"
	"reflect"
)

// TypeMap is a hash-table-based mapping from types (types.Type) to
// arbitrary interface{} values.  The concrete types that implement
// the Type interface are pointers.  Since they are not canonicalized,
// == cannot be used to check for equivalence, and thus we cannot
// simply use a Go map.
//
// Just as with map[K]V, a nil *TypeMap is a valid empty map.
//
// Not thread-safe.
//
type TypeMap struct {
	hasher Hasher             // shared by many Maps
	table  map[uint32][]entry // maps hash to bucket; entry.key==nil means unused
	length int                // number of map entries
}

// entry is an entry (key/value association) in a hash bucket.
type entry struct {
	key   Type
	value interface{}
}

// SetHasher sets the hasher used by Map.
//
// All Hashers are functionally equivalent but contain internal state
// used to cache the results of hashing previously seen types.
//
// A single Hasher created by MakeHasher() may be shared among many
// Maps.  This is recommended if the instances have many keys in
// common, as it will amortize the cost of hash computation.
//
// A Hasher may grow without bound as new types are seen.  Even when a
// type is deleted from the map, the Hasher never shrinks, since other
// types in the map may reference the deleted type indirectly.
//
// Hashers are not thread-safe, and read-only operations such as
// Map.Lookup require updates to the hasher, so a full Mutex lock (not a
// read-lock) is require around all Map operations if a shared
// hasher is accessed from multiple threads.
//
// If SetHasher is not called, the Map will create a private hasher at
// the first call to Insert.
//
func (m *TypeMap) SetHasher(hasher Hasher) {
	m.hasher = hasher
}

// Delete removes the entry with the given key, if any.
// It returns true if the entry was found.
//
func (m *TypeMap) Delete(key Type) bool {
	if m != nil && m.table != nil {
		hash := m.hasher.Hash(key)
		bucket := m.table[hash]
		for i, e := range bucket {
			if e.key != nil && Identical(key, e.key) {
				// We can't compact the bucket as it
				// would disturb iterators.
				bucket[i] = entry{}
				m.length--
				return true
			}
		}
	}
	return false
}

// At returns the map entry for the given key.
// The result is nil if the entry is not present.
//
func (m *TypeMap) At(key Type) interface{} {
	if m != nil && m.table != nil {
		for _, e := range m.table[m.hasher.Hash(key)] {
			if e.key != nil && Identical(key, e.key) {
				return e.value
			}
		}
	}
	return nil
}

// Set sets the map entry for key to val,
// and returns the previous entry, if any.
func (m *TypeMap) Set(key Type, value interface{}) (prev interface{}) {
	if m.table != nil {
		hash := m.hasher.Hash(key)
		bucket := m.table[hash]
		var hole *entry
		for i, e := range bucket {
			if e.key == nil {
				hole = &bucket[i]
			} else if Identical(key, e.key) {
				prev = e.value
				bucket[i].value = value
				return
			}
		}

		if hole != nil {
			*hole = entry{key, value} // overwrite deleted entry
		} else {
			m.table[hash] = append(bucket, entry{key, value})
		}
	} else {
		if m.hasher.memo == nil {
			m.hasher = MakeHasher()
		}
		hash := m.hasher.Hash(key)
		m.table = map[uint32][]entry{hash: {entry{key, value}}}
	}

	m.length++
	return
}

// Len returns the number of map entries.
func (m *TypeMap) Len() int {
	if m != nil {
		return m.length
	}
	return 0
}

// Iterate calls function f on each entry in the map in unspecified order.
//
// If f should mutate the map, Iterate provides the same guarantees as
// Go maps: if f deletes a map entry that Iterate has not yet reached,
// f will not be invoked for it, but if f inserts a map entry that
// Iterate has not yet reached, whether or not f will be invoked for
// it is unspecified.
//
func (m *TypeMap) Iterate(f func(key Type, value interface{})) {
	if m != nil {
		for _, bucket := range m.table {
			for _, e := range bucket {
				if e.key != nil {
					f(e.key, e.value)
				}
			}
		}
	}
}

// Keys returns a new slice containing the set of map keys.
// The order is unspecified.
func (m *TypeMap) Keys() []Type {
	keys := make([]Type, 0, m.Len())
	m.Iterate(func(key Type, _ interface{}) {
		keys = append(keys, key)
	})
	return keys
}

func (m *TypeMap) toString(values bool) string {
	if m == nil {
		return "{}"
	}
	var buf bytes.Buffer
	fmt.Fprint(&buf, "{")
	sep := ""
	m.Iterate(func(key Type, value interface{}) {
		fmt.Fprint(&buf, sep)
		sep = ", "
		fmt.Fprint(&buf, key)
		if values {
			fmt.Fprintf(&buf, ": %q", value)
		}
	})
	fmt.Fprint(&buf, "}")
	return buf.String()
}

// String returns a string representation of the map's entries.
// Values are printed using fmt.Sprintf("%v", v).
// Order is unspecified.
//
func (m *TypeMap) String() string {
	return m.toString(true)
}

// KeysString returns a string representation of the map's key set.
// Order is unspecified.
//
func (m *TypeMap) KeysString() string {
	return m.toString(false)
}

////////////////////////////////////////////////////////////////////////
// Hasher

// A Hasher maps each type to its hash value.
// For efficiency, a hasher uses memoization; thus its memory
// footprint grows monotonically over time.
// Hashers are not thread-safe.
// Hashers have reference semantics.
// Call MakeHasher to create a Hasher.
type Hasher struct {
	memo map[Type]uint32
}

// MakeHasher returns a new Hasher instance.
func MakeHasher() Hasher {
	return Hasher{make(map[Type]uint32)}
}

// Hash computes a hash value for the given type t such that
// Identical(t, t') => Hash(t) == Hash(t').
func (h Hasher) Hash(t Type) uint32 {
	hash, ok := h.memo[t]
	if !ok {
		hash = h.hashFor(t)
		h.memo[t] = hash
	}
	return hash
}

// hashString computes the Fowler–Noll–Vo hash of s.
func hashString(s string) uint32 {
	var h uint32
	for i := 0; i < len(s); i++ {
		h ^= uint32(s[i])
		h *= 16777619
	}
	return h
}

// hashFor computes the hash of t.
func (h Hasher) hashFor(t Type) uint32 {
	// See Identical for rationale.
	switch t := t.(type) {
	case *Basic:
		return uint32(t.Kind())

	case *Array:
		return 9043 + 2*uint32(t.Len()) + 3*h.Hash(t.Elem())

	case *Slice:
		return 9049 + 2*h.Hash(t.Elem())

	case *Struct:
		var hash uint32 = 9059
		for i, n := 0, t.NumFields(); i < n; i++ {
			f := t.Field(i)
			if f.Anonymous() {
				hash += 8861
			}
			hash += hashString(t.Tag(i))
			hash += hashString(f.Name()) // (ignore f.Pkg)
			hash += h.Hash(f.Type())
		}
		return hash

	case *Pointer:
		return 9067 + 2*h.Hash(t.Elem())

	case *Signature:
		var hash uint32 = 9091
		if t.Variadic() {
			hash *= 8863
		}
		return hash + 3*h.hashTuple(t.Params()) + 5*h.hashTuple(t.Results())

	case *Interface:
		var hash uint32 = 9103
		for i, n := 0, t.NumMethods(); i < n; i++ {
			// See go/types.identicalMethods for rationale.
			// Method order is not significant.
			// Ignore m.Pkg().
			m := t.Method(i)
			hash += 3*hashString(m.Name()) + 5*h.Hash(m.Type())
		}
		return hash

	case *Map:
		return 9109 + 2*h.Hash(t.Key()) + 3*h.Hash(t.Elem())

	case *Chan:
		return 9127 + 2*uint32(t.Dir()) + 3*h.Hash(t.Elem())

	case *Named:
		// Not safe with a copying GC; objects may move.
		return uint32(reflect.ValueOf(t.Obj()).Pointer())

	case *Tuple:
		return h.hashTuple(t)

	case *TypeParam:
		// Not safe with a copying GC; objects may move.
		return uint32(reflect.ValueOf(t.Obj()).Pointer())
	}

	panic(t)
}

func (h Hasher) hashTuple(tuple *Tuple) uint32 {
	// See go/types.identicalTypes for rationale.
	n := tuple.Len()
	var hash uint32 = 9137 + 2*uint32(n)
	for i := 0; i < n; i++ {
		hash += 3 * h.Hash(tuple.At(i).Type())
	}
	return hash
}
