"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.assertExhaustive = assertExhaustive;
exports.assert = assert;
exports.allSatisfy = allSatisfy;
const types_1 = require("./types");
function getAllProperties(obj) {
    const properties = new Set();
    do {
        for (const key of Reflect.ownKeys(obj)) {
            properties.add([obj, key]);
        }
    } while ((obj = Reflect.getPrototypeOf(obj)) && obj !== Object.prototype);
    return properties;
}
/**
 * Use to ensure that switches are checked to be exhaustive at compile time
 *
 * @example Basic usage
 * ```typescript
 * enum Something {
 *  left,
 *  right,
 * };
 * const something = getSomething();
 * switch (something) {
 *  case Something.left:
 *    ...
 *  case Something.right:
 *    ...
 *  default:
 *    assertExhaustive(something);
 * }
 * ```
 *
 * @param x - The param on which the switch operates
 */
function assertExhaustive(x) {
    throw new Error('Unexpected code execution detected, should be caught at compile time');
}
function assert(condition, reason) {
    if (!condition) {
        throw new types_1.Z3AssertionError(reason ?? 'Assertion failed');
    }
}
/**
 * Check the all elements of a `collection` satisfy the `premise`.
 * If any of the items fail the `premise`, returns false;
 * @returns null if the `collection` is empty, boolean otherwise
 */
function allSatisfy(collection, premise) {
    let hasItems = false;
    for (const arg of collection) {
        hasItems = true;
        if (!premise(arg)) {
            return false;
        }
    }
    return hasItems === true ? true : null;
}
