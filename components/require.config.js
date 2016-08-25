var components = {
    "packages": [
        {
            "name": "govuk_frontend_toolkit",
            "main": "govuk_frontend_toolkit-built.js"
        }
    ],
    "baseUrl": "components"
};
if (typeof require !== "undefined" && require.config) {
    require.config(components);
} else {
    var require = components;
}
if (typeof exports !== "undefined" && typeof module !== "undefined") {
    module.exports = components;
}