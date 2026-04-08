# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.2.0]

### Added

- `wildcard_iter` that supports \* (any) and ? (one) wildcards in search pattern

### Changed

- `iter_prefix` and `iter_prefix_mut` is more permissive in the generic key types it accepts

## [1.1.1]

### Fixed

- fixed >255 len nodes where there is a partial match

### Added

- `lcp_by4`/`lcp_by8`

### Changed

- `fmt::Debug` output look

## [1.1.0]

### Added

- trait impl BorrowedBytes for static sized arrays
- `entry` API for tree/map

### Changed

- allow for key lens greater than 255

### Removed

- unused trait methods in BorrowedBytes
