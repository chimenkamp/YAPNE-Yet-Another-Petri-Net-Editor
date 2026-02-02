
// WebPPL Browser Wrapper
// Exposes WebPPL as window.webppl for use in YAPNE

var webppl = require('webppl/src/browser.js');

// Expose to global scope
if (typeof window !== 'undefined') {
    window.webppl = webppl;
}
if (typeof global !== 'undefined') {
    global.webppl = webppl;
}

module.exports = webppl;
