// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// anyBuffer is similar to bytes.Buffer, but holds any values instead
// of just bytes.
type anyBuffer struct {
	buf []interface{} // contents are buf[off:]
	off int           // read at &buf[off], write at &buf[len(buf)]
}

// Reset resets the buffer to be empty.
func (b *anyBuffer) Reset() {
	b.buf = b.buf[:0]
	b.off = 0

	s := b.buf[:cap(b.buf)]
	for i := range s {
		s[i] = nil // release for GC
	}
}

// WriteAny appends x to the buffer, growing the buffer as needed.
func (b *anyBuffer) WriteAny(x interface{}) {
	b.buf = append(b.buf, x)
}

// ReadAny reads and returns the next value from the buffer.
// If no value is available, it panics.
func (b *anyBuffer) ReadAny() interface{} {
	res := b.buf[b.off]
	b.off++
	return res
}
