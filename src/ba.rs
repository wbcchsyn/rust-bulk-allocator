// Copyright 2020 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of rust-bulk-allocator
//
//  rust-bulk-allocator is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  rust-bulk-allocator is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with rust-bulk-allocator.  If not, see <http://www.gnu.org/licenses/>.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::PtrList;
use core::mem::size_of;

/// Inner type of 'Ba' and 'Uba'.
pub struct Cache {
    to_free: PtrList,
    pools: [PtrList; Self::POOLS_LEN],
}

impl Cache {
    pub const MAX_CACHE_SIZE: usize = 4096; // 4 KB.
    pub const MIN_CACHE_SIZE: usize = size_of::<PtrList>();
    const POOLS_LEN: usize =
        (Self::MIN_CACHE_SIZE.leading_zeros() - Self::MAX_CACHE_SIZE.leading_zeros() + 1) as usize;
}
