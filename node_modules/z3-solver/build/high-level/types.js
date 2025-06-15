"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Z3AssertionError = exports.Z3Error = void 0;
/**
 * Used to create a Real constant
 *
 * ```typescript
 * const x = from({ numerator: 1, denominator: 3 })
 *
 * x
 * // 1/3
 * isReal(x)
 * // true
 * isRealVal(x)
 * // true
 * x.asNumber()
 * // 0.3333333333333333
 * ```
 * @see {@link Context.from}
 * @category Global
 */
class Z3Error extends Error {
}
exports.Z3Error = Z3Error;
class Z3AssertionError extends Z3Error {
}
exports.Z3AssertionError = Z3AssertionError;
