# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)

## 0.1.0 - 2020-07-24
### Added
- First release

## 0.2.0 - 2020-09-04
### Fixed
- Update for feature 'allocator\_api' change.
- Refactor.

## 0.3.0 - 2021-01-29
### Updated
- Delete most codes and quit to enable nightly features.
- Give up to implementing `AllocRef` , and implements `GlobalAlloc` instead.

## 0.4.0 - 2023-02-24
### Added
- struct BulkAlloc
- struct LayoutBulkAlloc
- struct UnsafeLayoutBulkAlloc
### Removed
- struct BulkA
- struct LayoutBulkA
- struct UnBulkA
- struct UnLayoutBulkA

## 0.4.1 - 2023-02-25
### Changed
- Document

## 0.5.0 - 2023-08-14
### Changed
- Improve struct BulkAlloc
- The value of constant MEMORY\_CHANK\_SIZE
