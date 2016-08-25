/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.5 Copyright (c) 2010-2012, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */

var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.5',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && navigator && document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value !== 'string') {
                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    //Allow getting a global that expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite and existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; ary[i]; i += 1) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    if (i === 1 && (ary[2] === '..' || ary[0] === '..')) {
                        //End of the line. Keep at least one non-dot
                        //path segment at the front so it can be mapped
                        //correctly to disk. Otherwise, there is likely
                        //no path mapping for a path starting with '..'.
                        //This can still fail, but catches the most reasonable
                        //uses of ..
                        break;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgName, pkgConfig, mapValue, nameParts, i, j, nameSegment,
                foundMap, foundI, foundStarMap, starI,
                baseParts = baseName && baseName.split('/'),
                normalizedBaseParts = baseParts,
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name && name.charAt(0) === '.') {
                //If have a base name, try to normalize against it,
                //otherwise, assume it is a top-level require that will
                //be relative to baseUrl in the end.
                if (baseName) {
                    if (getOwn(config.pkgs, baseName)) {
                        //If the baseName is a package name, then just treat it as one
                        //name to concat the name with.
                        normalizedBaseParts = baseParts = [baseName];
                    } else {
                        //Convert baseName to array, and lop off the last part,
                        //so that . matches that 'directory' and not name of the baseName's
                        //module. For instance, baseName of 'one/two/three', maps to
                        //'one/two/three.js', but we want the directory, 'one/two' for
                        //this normalization.
                        normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    }

                    name = normalizedBaseParts.concat(name.split('/'));
                    trimDots(name);

                    //Some use of packages may use a . path to reference the
                    //'main' module name, so normalize for that.
                    pkgConfig = getOwn(config.pkgs, (pkgName = name[0]));
                    name = name.join('/');
                    if (pkgConfig && name === pkgName + '/' + pkgConfig.main) {
                        name = pkgName;
                    }
                } else if (name.indexOf('./') === 0) {
                    // No baseName, so this is ID is resolved relative
                    // to baseUrl, pull off the leading dot.
                    name = name.substring(2);
                }
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break;
                                }
                            }
                        }
                    }

                    if (foundMap) {
                        break;
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            return name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                removeScript(id);
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);
                context.require([id]);
                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        normalizedName = normalize(name, parentName, applyMap);
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                getModule(depMap).on(name, fn);
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length - 1, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return mod.exports;
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return (config.config && getOwn(config.config, mod.map.id)) || {};
                        },
                        exports: defined[mod.map.id]
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var map, modId, err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                map = mod.map;
                modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error.
                            if (this.events.error) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            if (this.map.isDefine) {
                                //If setting exports via 'module' is in play,
                                //favor that over return value and exports. After that,
                                //favor a non-undefined return value over exports use.
                                cjsModule = this.module;
                                if (cjsModule &&
                                        cjsModule.exports !== undefined &&
                                        //Make sure it is not already the exports value
                                        cjsModule.exports !== this.exports) {
                                    exports = cjsModule.exports;
                                } else if (exports === undefined && this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = [this.map.id];
                                err.requireType = 'define';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', this.errback);
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths and packages since they require special processing,
                //they are additive.
                var pkgs = config.pkgs,
                    shim = config.shim,
                    objs = {
                        paths: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (prop === 'map') {
                            if (!config.map) {
                                config.map = {};
                            }
                            mixin(config[prop], value, true, true);
                        } else {
                            mixin(config[prop], value, true);
                        }
                    } else {
                        config[prop] = value;
                    }
                });

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;
                        location = pkgObj.location;

                        //Create a brand new object on pkgs, since currentPackages can
                        //be passed in again, and config.pkgs is the internal transformed
                        //state for all package configs.
                        pkgs[pkgObj.name] = {
                            name: pkgObj.name,
                            location: location || pkgObj.name,
                            //Remove leading dot in main, so main paths are normalized,
                            //and remove any trailing .js, since different package
                            //envs have different conventions: some use a module name,
                            //some use a file name.
                            main: (pkgObj.main || 'main')
                                  .replace(currDirRegExp, '')
                                  .replace(jsSuffixRegExp, '')
                        };
                    });

                    //Done with modifications, assing packages back to context config
                    config.pkgs = pkgs;
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overriden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, pkgs, pkg, pkgPath, syms, i, parentModule, url,
                    parentPath;

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;
                    pkgs = config.pkgs;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');
                        pkg = getOwn(pkgs, parentModule);
                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        } else if (pkg) {
                            //If module name is just the package name, then looking
                            //for the main module.
                            if (moduleName === pkg.name) {
                                pkgPath = pkg.location + '/' + pkg.main;
                            } else {
                                pkgPath = pkg.location;
                            }
                            syms.splice(0, i, pkgPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callack function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error', evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = function (err) {
        throw err;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = config.xhtml ?
                    document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                    document.createElement('script');
            node.type = config.scriptType || 'text/javascript';
            node.charset = 'utf-8';
            node.async = true;

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation that a build has been done so that
                //only one script needs to be loaded anyway. This may need to be
                //reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = dataMain.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                    dataMain = mainScript;
                }

                //Strip off any trailing .js since dataMain is now
                //like a module name.
                dataMain = dataMain.replace(jsSuffixRegExp, '');

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(dataMain) : [dataMain];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = [];
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps.length && isFunction(callback)) {
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

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
define('govuk_frontend_toolkit', function (require, exports, module) {
//= require_tree ./govuk

// Stageprompt 2.0.1
//
// See: https://github.com/alphagov/stageprompt
//
// Stageprompt allows user journeys to be described and instrumented
// using data attributes.
//
// Setup (run this on document ready):
//
//   GOVUK.performance.stageprompt.setupForGoogleAnalytics();
//
// Usage:
//
//   Sending events on page load:
//
//     <div id="wrapper" class="service" data-journey="pay-register-birth-abroad:start">
//         [...]
//     </div>
//
//   Sending events on click:
//
//     <a class="help-button" href="#" data-journey-click="stage:help:info">See more info...</a>

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  GOVUK.performance = GOVUK.performance || {};

  GOVUK.performance.stageprompt = (function () {

    var setup, setupForGoogleAnalytics, splitAction;

    splitAction = function (action) {
      var parts = action.split(':');
      if (parts.length <= 3) return parts;
      return [parts.shift(), parts.shift(), parts.join(':')];
    };

    setup = function (analyticsCallback) {
      var journeyStage = $('[data-journey]').attr('data-journey'),
          journeyHelpers = $('[data-journey-click]');

      if (journeyStage) {
        analyticsCallback.apply(null, splitAction(journeyStage));
      }

      journeyHelpers.on('click', function (event) {
        analyticsCallback.apply(null, splitAction($(this).data('journey-click')));
      });
    };

    setupForGoogleAnalytics = function () {
      setup(GOVUK.performance.sendGoogleAnalyticsEvent);
    };

    return {
      setup: setup,
      setupForGoogleAnalytics: setupForGoogleAnalytics
    };
  }());

  GOVUK.performance.sendGoogleAnalyticsEvent = function (category, event, label) {
    _gaq.push(['_trackEvent', category, event, label, undefined, true]);
  };

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};
  GOVUK.Modules = GOVUK.Modules || {};

  GOVUK.modules = {
    find: function(container) {
      var modules,
          moduleSelector = '[data-module]',
          container = container || $('body');

      modules = container.find(moduleSelector);

      // Container could be a module too
      if (container.is(moduleSelector)) {
        modules = modules.add(container);
      }

      return modules;
    },

    start: function(container) {
      var modules = this.find(container);

      for (var i = 0, l = modules.length; i < l; i++) {
        var module,
            element = $(modules[i]),
            type = camelCaseAndCapitalise(element.data('module')),
            started = element.data('module-started');

        if (typeof GOVUK.Modules[type] === "function" && !started) {
          module = new GOVUK.Modules[type]();
          module.start(element);
          element.data('module-started', true);
        }
      }

      // eg selectable-table to SelectableTable
      function camelCaseAndCapitalise(string) {
        return capitaliseFirstLetter(camelCase(string));
      }

      // http://stackoverflow.com/questions/6660977/convert-hyphens-to-camel-case-camelcase
      function camelCase(string) {
        return string.replace(/-([a-z])/g, function (g) {
          return g[1].toUpperCase();
        });
      }

      // http://stackoverflow.com/questions/1026069/capitalize-the-first-letter-of-string-in-javascript
      function capitaliseFirstLetter(string) {
        return string.charAt(0).toUpperCase() + string.slice(1);
      }
    }
  }

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  // A multivariate test framework
  //
  // Based loosely on https://github.com/jamesyu/cohorts
  //
  // Full documentation is in README.md.
  //
  function MultivariateTest(options) {
    this.$el = $(options.el);
    this._loadOption(options, 'name');
    this._loadOption(options, 'customDimensionIndex', null);
    this._loadOption(options, 'cohorts');
    this._loadOption(options, 'runImmediately', true);
    this._loadOption(options, 'defaultWeight', 1);
    this._loadOption(options, 'contentExperimentId', null);
    this._loadOption(options, 'cookieDuration', 30);

    if (this.runImmediately) {
      this.run();
    }
  }

  MultivariateTest.prototype._loadOption = function(options, key, defaultValue) {
    if (options[key] !== undefined) {
      this[key] = options[key];
    }
    if (this[key] === undefined) {
      if (defaultValue === undefined) {
        throw new Error(key+" option is required for a multivariate test");
      }
      else {
        this[key] = defaultValue;
      }
    }
  };

  MultivariateTest.prototype.run = function() {
    var cohort = this.getCohort();
    if (cohort) {
      this.setUpContentExperiment(cohort);
      this.setCustomVar(cohort);
      this.executeCohort(cohort);
      this.createDummyEvent(cohort);
    }
  };

  MultivariateTest.prototype.executeCohort = function(cohort) {
    var cohortObj = this.cohorts[cohort];
    if (cohortObj.callback) {
      if (typeof cohortObj.callback === "string") {
        this[cohortObj.callback]();
      }
      else {
        cohortObj.callback();
      }
    }
    if (cohortObj.html) {
      this.$el.html(cohortObj.html);
      this.$el.show();
    }
  };

  // Get the current cohort or assign one if it has not been already
  MultivariateTest.prototype.getCohort = function() {
    var cohort = GOVUK.cookie(this.cookieName());
    if (!cohort || !this.cohorts[cohort]) {
      cohort = this.chooseRandomCohort();
      GOVUK.cookie(this.cookieName(), cohort, {days: this.cookieDuration});
    }
    return cohort;
  };

  MultivariateTest.prototype.setCustomVar = function(cohort) {
    if (this.customDimensionIndex &&
      this.customDimensionIndex.constructor === Array) {
      for (var index = 0; index < this.customDimensionIndex.length; index++) {
        this.setDimension(cohort, this.customDimensionIndex[index])
      }
    } else if (this.customDimensionIndex) {
      this.setDimension(cohort, this.customDimensionIndex)
    }
  };

  MultivariateTest.prototype.setDimension = function(cohort, dimension) {
    GOVUK.analytics.setDimension(
      dimension,
      this.cookieName() + "__" + cohort
    );
  };

  MultivariateTest.prototype.setUpContentExperiment = function(cohort) {
    var contentExperimentId = this.contentExperimentId;
    var cohortVariantId = this.cohorts[cohort]['variantId'];
    if(typeof contentExperimentId !== 'undefined' &&
      typeof cohortVariantId !== 'undefined' &&
      typeof window.ga === "function"){
      window.ga('set', 'expId', contentExperimentId);
      window.ga('set', 'expVar', cohortVariantId);
    };
  };

  MultivariateTest.prototype.createDummyEvent = function(cohort) {
    // Fire off a dummy event to set the custom var and the content experiment on the page.
    // Ideally we'd be able to call setCustomVar before trackPageview,
    // but would need reordering the existing GA code.
    GOVUK.analytics.trackEvent(this.cookieName(), 'run', {nonInteraction:true});
  };

  MultivariateTest.prototype.weightedCohortNames = function() {
    var names = [],
        defaultWeight = this.defaultWeight;

    $.each(this.cohorts, function(key, cohortSettings) {
      var numberForCohort, i;

      if (typeof cohortSettings.weight === 'undefined'){
        numberForCohort = defaultWeight;
      } else {
        numberForCohort = cohortSettings.weight;
      }

      for(i=0; i<numberForCohort; i++){
        names.push(key);
      }
    });

    return names;
  };

  MultivariateTest.prototype.chooseRandomCohort = function() {
    var names = this.weightedCohortNames();
    return names[Math.floor(Math.random() * names.length)];
  };

  MultivariateTest.prototype.cookieName = function() {
    return "multivariatetest_cohort_" + this.name;
  };

  GOVUK.MultivariateTest = MultivariateTest;

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  // Only show the first {n} items in a list, documentation is in the README.md
  var PrimaryList = function(el, selector){
    this.$el = $(el);
    this.$extraLinks = this.$el.find('li:not('+selector+')');
    // only hide more than one extra link
    if(this.$extraLinks.length > 1){
      this.addToggleLink();
      this.hideExtraLinks();
    }
  };
  PrimaryList.prototype = {
    toggleText: function(){
      if(this.$extraLinks.length > 1){
        return '+'+ this.$extraLinks.length +' others';
      } else {
        return '+'+ this.$extraLinks.length +' other';
      }
    },
    addToggleLink: function(){
      this.$toggleLink = $('<a href="#">'+ this.toggleText() + '</a>');
      this.$toggleLink.click($.proxy(this.toggleLinks, this));
      this.$toggleLink.insertAfter(this.$el);
    },
    toggleLinks: function(e){
      e.preventDefault();
      this.$toggleLink.remove();
      this.showExtraLinks();
    },
    hideExtraLinks: function(){
      this.$extraLinks.addClass('visuallyhidden');
      $(window).trigger('govuk.pageSizeChanged');
    },
    showExtraLinks: function(){
      this.$extraLinks.removeClass('visuallyhidden');
      $(window).trigger('govuk.pageSizeChanged');
    }
  };

  GOVUK.PrimaryList = PrimaryList;

  GOVUK.primaryLinks = {
    init: function(selector){
      $(selector).parent().each(function(i, el){
        new GOVUK.PrimaryList(el, selector);
      });
    }
  };

  global.GOVUK = GOVUK;
})(window);

(function (global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  var SelectionButtons = function (elmsOrSelector, opts) {

    this.selectedClass = 'selected';
    this.focusedClass = 'focused';
    if (opts !== undefined) {
      $.each(opts, function (optionName, optionObj) {
        this[optionName] = optionObj;
      }.bind(this));
    }
    if (typeof elmsOrSelector === 'string') {
      this.selector = elmsOrSelector;
      this.setInitialState($(this.selector));
    } else if (elmsOrSelector !== undefined) {
      this.$elms = elmsOrSelector;
      this.setInitialState(this.$elms);
    }
    this.addEvents();
  };
  SelectionButtons.prototype.addEvents = function () {
    if (typeof this.$elms !== 'undefined') {
      this.addElementLevelEvents();
    } else {
      this.addDocumentLevelEvents();
    }
  };
  SelectionButtons.prototype.setInitialState = function ($elms) {
    $elms.each(function (idx, elm) {
      var $elm = $(elm);

      if ($elm.is(':checked')) {
        this.markSelected($elm);
      }
    }.bind(this));
  };
  SelectionButtons.prototype.markFocused = function ($elm, state) {
    if (state === 'focused') {
      $elm.parent('label').addClass(this.focusedClass);
    } else {
      $elm.parent('label').removeClass(this.focusedClass);
    }
  };
  SelectionButtons.prototype.markSelected = function ($elm) {
    var radioName;

    if ($elm.attr('type') === 'radio') {
      radioName = $elm.attr('name');
      $($elm[0].form).find('input[name="' + radioName + '"]')
        .parent('label')
        .removeClass(this.selectedClass);
      $elm.parent('label').addClass(this.selectedClass);
    } else { // checkbox
      if ($elm.is(':checked')) {
        $elm.parent('label').addClass(this.selectedClass);
      } else {
        $elm.parent('label').removeClass(this.selectedClass);
      }
    }
  };
  SelectionButtons.prototype.addElementLevelEvents = function () {
    this.clickHandler = this.getClickHandler();
    this.focusHandler = this.getFocusHandler({ 'level' : 'element' });

    this.$elms
      .on('click', this.clickHandler)
      .on('focus blur', this.focusHandler);
  };
  SelectionButtons.prototype.addDocumentLevelEvents = function () {
    this.clickHandler = this.getClickHandler();
    this.focusHandler = this.getFocusHandler({ 'level' : 'document' });

    $(document)
      .on('click', this.selector, this.clickHandler)
      .on('focus blur', this.selector, this.focusHandler);
  };
  SelectionButtons.prototype.getClickHandler = function () {
    return function (e) {
      this.markSelected($(e.target));
    }.bind(this);
  };
  SelectionButtons.prototype.getFocusHandler = function (opts) {
    var focusEvent = (opts.level === 'document') ? 'focusin' : 'focus';

    return function (e) {
      var state = (e.type === focusEvent) ? 'focused' : 'blurred';

      this.markFocused($(e.target), state);
    }.bind(this);
  };
  SelectionButtons.prototype.destroy = function () {
    if (typeof this.selector !== 'undefined') {
      $(document)
        .off('click', this.selector, this.clickHandler)
        .off('focus blur', this.selector, this.focusHandler);
    } else {
      this.$elms
        .off('click', this.clickHandler)
        .off('focus blur', this.focusHandler);
    }
  };

  GOVUK.SelectionButtons = SelectionButtons;
  global.GOVUK = GOVUK;
})(window);

// javascript 'shim' to trigger the click event of element(s)
// when the space key is pressed.
//
// usage instructions:
// GOVUK.shimLinksWithButtonRole.init();
//
// If you want to customise the shim you can pass in a custom configuration
// object with your own selector for the target elements and addional keyup
// codes if there becomes a need to do so. For example:
// GOVUK.shimLinksWithButtonRole.init({ selector: '[role="button"]' });
(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  GOVUK.shimLinksWithButtonRole = {

    // default configuration that can be overridden by passing object as second parameter to module
    config: {
      // the target element(s) to attach the shim event to
      selector: 'a[role="button"]',
      // array of keys to match against upon the keyup event
      keycodes: [
        32 // spacekey
      ],
    },

    // event behaviour (not a typical anonymous function for resuse if needed)
    triggerClickOnTarget: function triggerClickOnTarget(event) {
      // if the code from this event is in the keycodes array then
      if ($.inArray(event.which, this.config.keycodes) !== -1) {
        event.preventDefault();
        // trigger the target's click event
        event.target.click();
      }
    },

    // By default this will find all links with role attribute set to
    // 'button' and will trigger their click event when the space key (32) is pressed.
    // @method init
    // @param  {Object}   customConfig                object to override default configuration
    //         {String}   customConfig.selector       a selector for the elements to be 'clicked'
    //         {Array}    customConfig.keycodes       an array of javascript keycode values to match against that when pressed will trigger the click
    init: function init(customConfig) {
      // extend the default config with any custom attributes passed in
      this.config = $.extend(this.config, customConfig);
      // if we have found elements then:
      if($(this.config.selector).length > 0) {
        // listen to 'document' for keyup event on the elements and fire the triggerClickOnTarget
        $(document).on('keyup', this.config.selector, this.triggerClickOnTarget.bind(this));
      }
    }

  };

  // hand back to global
  global.GOVUK = GOVUK;

})(window);

(function (global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  // Stick elements to top of screen when you scroll past, documentation is in the README.md
  var sticky = {
    _hasScrolled: false,
    _scrollTimeout: false,

    init: function(){
      var $els = $('.js-stick-at-top-when-scrolling');

      if($els.length > 0){
        sticky.$els = $els;

        if(sticky._scrollTimeout === false) {
          $(global).scroll(sticky.onScroll);
          sticky._scrollTimeout = global.setInterval(sticky.checkScroll, 50);
        }
        $(global).resize(sticky.onResize);
      }
      if(GOVUK.stopScrollingAtFooter){
        $els.each(function(i,el){
          var $img = $(el).find('img');
          if($img.length > 0){
            var image = new Image();
            image.onload = function(){
              GOVUK.stopScrollingAtFooter.addEl($(el), $(el).outerHeight());
            };
            image.src = $img.attr('src');
          } else {
            GOVUK.stopScrollingAtFooter.addEl($(el), $(el).outerHeight());
          }
        });
      }
    },
    onScroll: function(){
      sticky._hasScrolled = true;
    },
    checkScroll: function(){
      if(sticky._hasScrolled === true){
        sticky._hasScrolled = false;

        var windowVerticalPosition = $(global).scrollTop();
        sticky.$els.each(function(i, el){
          var $el = $(el),
              scrolledFrom = $el.data('scrolled-from');

          if (scrolledFrom && windowVerticalPosition < scrolledFrom){
            sticky.release($el);
          } else if($(global).width() > 768 && windowVerticalPosition >= $el.offset().top) {
            sticky.stick($el);
          }
        });
      }
    },
    stick: function($el){
      if (!$el.hasClass('content-fixed')) {
        $el.data('scrolled-from', $el.offset().top);
        var height = Math.max($el.height(), 1);
        $el.before('<div class="shim" style="width: '+ $el.width() + 'px; height: ' + height + 'px">&nbsp;</div>');
        $el.css('width', $el.width() + "px").addClass('content-fixed');
      }
    },
    release: function($el){
      if($el.hasClass('content-fixed')){
        $el.data('scrolled-from', false);
        $el.removeClass('content-fixed').css('width', '');
        $el.siblings('.shim').remove();
      }
    }
  };
  GOVUK.stickAtTopWhenScrolling = sticky;
  global.GOVUK = GOVUK;
})(window);

// Stop scrolling at footer.
//
// This can be added to elements with `position: fixed` to stop them from
// overflowing on the footer.
//
// Usage:
//
//    GOVUK.stopScrollingAtFooter.addEl($(node), $(node).height());
//
// Height is passed in separatly incase the scrolling element has no height
// itself.


(function (global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  var stopScrollingAtFooter = {
    _pollingId: null,
    _isPolling: false,
    _hasScrollEvt: false,
    _els: [],

    addEl: function($fixedEl, height){
      var fixedOffset;

      if(!$fixedEl.length) { return; }

      fixedOffset = parseInt($fixedEl.css('top'), 10);
      fixedOffset = isNaN(fixedOffset) ? 0 : fixedOffset;

      stopScrollingAtFooter.updateFooterTop();
      $(global).on('govuk.pageSizeChanged', stopScrollingAtFooter.updateFooterTop);

      var $siblingEl = $('<div></div>');
      $siblingEl.insertBefore($fixedEl);
      var fixedTop = $siblingEl.offset().top - $siblingEl.position().top;
      $siblingEl.remove();

      var el = {
        $fixedEl: $fixedEl,
        height: height + fixedOffset,
        fixedTop: height + fixedTop,
        state: 'fixed'
      };
      stopScrollingAtFooter._els.push(el);

      stopScrollingAtFooter.initTimeout();
    },
    updateFooterTop: function(){
      var footer = $('.js-footer:eq(0)');
      if (footer.length === 0) {
        return 0;
      }
      stopScrollingAtFooter.footerTop = footer.offset().top - 10;
    },
    initTimeout: function(){
      if(stopScrollingAtFooter._hasScrollEvt === false) {
        $(window).scroll(stopScrollingAtFooter.onScroll);
        stopScrollingAtFooter._hasScrollEvt = true;
      }
    },
    onScroll: function(){
      if (stopScrollingAtFooter._isPolling === false) {
        stopScrollingAtFooter.startPolling();
      }
    },
    startPolling: (function(){
      if (window.requestAnimationFrame) {
        return (function(){
          var callback = function(){
            stopScrollingAtFooter.checkScroll();
            if (stopScrollingAtFooter._isPolling === true) {
              stopScrollingAtFooter.startPolling();
            }
          };
          stopScrollingAtFooter._pollingId = window.requestAnimationFrame(callback);
          stopScrollingAtFooter._isPolling = true;
        });
      } else {
        return (function(){
          stopScrollingAtFooter._pollingId = window.setInterval(stopScrollingAtFooter.checkScroll, 16);
          stopScrollingAtFooter._isPolling = true;
        });
      }
    }()),
    stopPolling: (function(){
      if (window.requestAnimationFrame) {
        return (function(){
          window.cancelAnimationFrame(stopScrollingAtFooter._pollingId);
          stopScrollingAtFooter._isPolling = false;
        });
      } else {
        return (function(){
          window.clearInterval(stopScrollingAtFooter._pollingId);
          stopScrollingAtFooter._isPolling = false;
        });
      }
    }()),
    checkScroll: function(){
      var cachedScrollTop = $(window).scrollTop();
      if ((cachedScrollTop < (stopScrollingAtFooter.cachedScrollTop + 2)) && (cachedScrollTop > (stopScrollingAtFooter.cachedScrollTop - 2))) {
        stopScrollingAtFooter.stopPolling();
        return;
      } else {
        stopScrollingAtFooter.cachedScrollTop = cachedScrollTop;
      }

      $.each(stopScrollingAtFooter._els, function(i, el){
        var bottomOfEl = cachedScrollTop + el.height;

        if (bottomOfEl > stopScrollingAtFooter.footerTop){
          stopScrollingAtFooter.stick(el);
        } else {
          stopScrollingAtFooter.unstick(el);
        }
      });
    },
    stick: function(el){
      if(el.state === 'fixed' && el.$fixedEl.css('position') === 'fixed'){
        el.$fixedEl.css({ 'position': 'absolute', 'top': stopScrollingAtFooter.footerTop - el.fixedTop });
        el.state = 'absolute';
      }
    },
    unstick: function(el){
      if(el.state === 'absolute'){
        el.$fixedEl.css({ 'position': '', 'top': '' });
        el.state = 'fixed';
      }
    }
  };

  GOVUK.stopScrollingAtFooter = stopScrollingAtFooter;

  $(global).load(function(){ $(global).trigger('govuk.pageSizeChanged'); });

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var GOVUK = global.GOVUK || {};

  // For usage and initialisation see:
  // https://github.com/alphagov/govuk_frontend_toolkit/blob/master/docs/analytics.md#create-an-analytics-tracker

  var Analytics = function(config) {
    this.trackers = [];
    if (typeof config.universalId != 'undefined') {
      var universalId = config.universalId;
      delete config.universalId;
      this.trackers.push(new GOVUK.GoogleAnalyticsUniversalTracker(universalId, config));
    }
  };

  Analytics.prototype.sendToTrackers = function(method, args) {
    for (var i = 0, l = this.trackers.length; i < l; i++) {
      var tracker = this.trackers[i],
          fn = tracker[method];

      if (typeof fn === "function") {
        fn.apply(tracker, args);
      }
    }
  };

  Analytics.load = function() {
    GOVUK.GoogleAnalyticsUniversalTracker.load();
  };

  Analytics.prototype.trackPageview = function(path, title, options) {
    this.sendToTrackers('trackPageview', arguments);
  };

  /*
    https://developers.google.com/analytics/devguides/collection/analyticsjs/events
    options.label – Useful for categorizing events (eg nav buttons)
    options.value – Values must be non-negative. Useful to pass counts
    options.nonInteraction – Prevent event from impacting bounce rate
  */
  Analytics.prototype.trackEvent = function(category, action, options) {
    this.sendToTrackers('trackEvent', arguments);
  };

  Analytics.prototype.trackShare = function(network) {
    this.sendToTrackers('trackSocial', [network, 'share', location.pathname]);
  };

  /*
    The custom dimension index must be configured within the
    Universal Analytics profile
   */
  Analytics.prototype.setDimension = function(index, value) {
    this.sendToTrackers('setDimension', arguments);
  };

  /*
   Add a beacon to track a page in another GA account on another domain.
   */
  Analytics.prototype.addLinkedTrackerDomain = function(trackerId, name, domain) {
    this.sendToTrackers('addLinkedTrackerDomain', arguments);
  };

  GOVUK.Analytics = Analytics;

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  GOVUK.analyticsPlugins = GOVUK.analyticsPlugins || {};
  GOVUK.analyticsPlugins.downloadLinkTracker = function (options) {
    var options = options || {},
        downloadLinkSelector = options.selector;

    if (downloadLinkSelector) {
      $('body').on('click', downloadLinkSelector, trackDownload);
    }

    function trackDownload(evt) {
      var $link = getLinkFromEvent(evt),
          href = $link.attr('href'),
          evtOptions = {transport: 'beacon'},
          linkText = $.trim($link.text());

      if (linkText) {
        evtOptions.label = linkText;
      }

      GOVUK.analytics.trackEvent('Download Link Clicked', href, evtOptions);
    }

    function getLinkFromEvent(evt) {
      var $target = $(evt.target);

      if (!$target.is('a')) {
        $target = $target.parents('a');
      }

      return $target;
    }
  }

  global.GOVUK = GOVUK;
})(window);

// Extension to track errors using google analytics as a data store.
(function(global) {
  "use strict";

  var GOVUK = global.GOVUK || {};

  GOVUK.analyticsPlugins = GOVUK.analyticsPlugins || {};

  GOVUK.analyticsPlugins.error = function (options) {
    var options = options || {},
        filenameMustMatch = options.filenameMustMatch;

    var trackJavaScriptError = function (e) {
      var errorFilename = e.filename,
          errorSource = errorFilename + ': ' + e.lineno;

      if (shouldTrackThisError(errorFilename)) {
        GOVUK.analytics.trackEvent('JavaScript Error', e.message, {
          label: errorSource,
          value: 1,
          nonInteraction: true
        });
      }
    };

    function shouldTrackThisError(errorFilename) {
      // Errors in page should always be tracked
      // If there's no filename filter, everything is tracked
      if (!errorFilename || !filenameMustMatch) {
        return true;
      }

      // If there's a filter and the error matches it, track it
      if (filenameMustMatch.test(errorFilename)) {
        return true;
      }

      return false;
    }

    if (global.addEventListener) {
      global.addEventListener('error', trackJavaScriptError, false);
    } else if (global.attachEvent) {
      global.attachEvent('onerror', trackJavaScriptError);
    } else {
      global.onerror = trackJavaScriptError;
    }
  }

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  GOVUK.analyticsPlugins = GOVUK.analyticsPlugins || {};
  GOVUK.analyticsPlugins.externalLinkTracker = function () {

    var currentHost = GOVUK.analyticsPlugins.externalLinkTracker.getHostname(),
        externalLinkSelector = 'a[href^="http"]:not(a[href*="' + currentHost + '"])';

    $('body').on('click', externalLinkSelector, trackClickEvent);

    function trackClickEvent(evt) {
      var $link = getLinkFromEvent(evt),
          options = {transport: 'beacon'},
          href = $link.attr('href'),
          linkText = $.trim($link.text());

      if (linkText) {
        options.label = linkText;
      }

      GOVUK.analytics.trackEvent('External Link Clicked', href, options);
    }

    function getLinkFromEvent(evt) {
      var $target = $(evt.target);

      if (!$target.is('a')) {
        $target = $target.parents('a');
      }

      return $target;
    }
  }

  GOVUK.analyticsPlugins.externalLinkTracker.getHostname = function() {
    return global.location.hostname;
  }

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var GOVUK = global.GOVUK || {};

  var GoogleAnalyticsUniversalTracker = function(trackingId, fieldsObject) {

    function configureProfile() {
      // https://developers.google.com/analytics/devguides/collection/analyticsjs/command-queue-reference#create
      sendToGa('create', trackingId, fieldsObject);
    }

    function anonymizeIp() {
      // https://developers.google.com/analytics/devguides/collection/analyticsjs/advanced#anonymizeip
      sendToGa('set', 'anonymizeIp', true);
    }

    // Support legacy cookieDomain param
    if (typeof fieldsObject === 'string') {
      fieldsObject = { cookieDomain: fieldsObject };
    }

    configureProfile();
    anonymizeIp();
  };

  GoogleAnalyticsUniversalTracker.load = function() {
    (function(i,s,o,g,r,a,m){i['GoogleAnalyticsObject']=r;i[r]=i[r]||function(){
        (i[r].q=i[r].q||[]).push(arguments)},i[r].l=1*new Date();a=s.createElement(o),
                             m=s.getElementsByTagName(o)[0];a.async=1;a.src=g;m.parentNode.insertBefore(a,m)
    })(global,document,'script','https://www.google-analytics.com/analytics.js','ga');
  };

  // https://developers.google.com/analytics/devguides/collection/analyticsjs/pages
  GoogleAnalyticsUniversalTracker.prototype.trackPageview = function(path, title, options) {
    var options = options || {};

    if (typeof path === "string") {
      var pageviewObject = {
            page: path
          };

      if (typeof title === "string") {
        pageviewObject.title = title;
      }

      // Set the transport method for the pageview
      // Typically used for enabling `navigator.sendBeacon` when the page might be unloading
      // https://developers.google.com/analytics/devguides/collection/analyticsjs/field-reference#transport
      if (options.transport) {
        pageviewObject.transport = options.transport;
      }

      sendToGa('send', 'pageview', pageviewObject);
    } else {
      sendToGa('send', 'pageview');
    }
  };

  // https://developers.google.com/analytics/devguides/collection/analyticsjs/events
  GoogleAnalyticsUniversalTracker.prototype.trackEvent = function(category, action, options) {
    var value,
        options = options || {},
        evt = {
          hitType: 'event',
          eventCategory: category,
          eventAction: action
        };

    // Label is optional
    if (typeof options.label === "string") {
      evt.eventLabel = options.label;
    }

    // Page is optional
    if (typeof options.page === "string") {
      evt.page = options.page;
    }

    // Value is optional, but when used must be an
    // integer, otherwise the event will be invalid
    // and not logged
    if (options.value || options.value === 0) {
      value = parseInt(options.value, 10);
      if (typeof value === "number" && !isNaN(value)) {
        evt.eventValue = value;
      }
    }

    // Prevents an event from affecting bounce rate
    // https://developers.google.com/analytics/devguides/collection/analyticsjs/events#implementation
    if (options.nonInteraction) {
      evt.nonInteraction = 1;
    }

    // Set the transport method for the event
    // Typically used for enabling `navigator.sendBeacon` when the page might be unloading
    // https://developers.google.com/analytics/devguides/collection/analyticsjs/field-reference#transport
    if (options.transport) {
      evt.transport = options.transport;
    }

    sendToGa('send', evt);
  };

  /*
    https://developers.google.com/analytics/devguides/collection/analyticsjs/social-interactions
    network – The network on which the action occurs (e.g. Facebook, Twitter)
    action – The type of action that happens (e.g. Like, Send, Tweet)
    target – Specifies the target of a social interaction.
             This value is typically a URL but can be any text.
  */
  GoogleAnalyticsUniversalTracker.prototype.trackSocial = function(network, action, target) {
    sendToGa('send', {
      'hitType': 'social',
      'socialNetwork': network,
      'socialAction': action,
      'socialTarget': target
    });
  };

  /*
   https://developers.google.com/analytics/devguides/collection/analyticsjs/cross-domain
   trackerId - the UA account code to track the domain against
   name      - name for the tracker
   domain    - the domain to track
  */
  GoogleAnalyticsUniversalTracker.prototype.addLinkedTrackerDomain = function(trackerId, name, domain) {
    sendToGa('create',
             trackerId,
             'auto',
             {'name': name});
    // Load the plugin.
    sendToGa('require', 'linker');
    sendToGa(name + '.require', 'linker');

    // Define which domains to autoLink.
    sendToGa('linker:autoLink', [domain]);
    sendToGa(name + '.linker:autoLink', [domain]);

    sendToGa(name + '.set', 'anonymizeIp', true);
    sendToGa(name + '.send', 'pageview');
  };

  // https://developers.google.com/analytics/devguides/collection/analyticsjs/custom-dims-mets
  GoogleAnalyticsUniversalTracker.prototype.setDimension = function(index, value) {
    sendToGa('set', 'dimension' + index, String(value));
  };

  function sendToGa() {
    if (typeof global.ga === "function") {
      ga.apply(global, arguments);
    }
  }

  GOVUK.GoogleAnalyticsUniversalTracker = GoogleAnalyticsUniversalTracker;

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var $ = global.jQuery;
  var GOVUK = global.GOVUK || {};

  GOVUK.analyticsPlugins = GOVUK.analyticsPlugins || {};
  GOVUK.analyticsPlugins.mailtoLinkTracker = function () {

    var mailtoLinkSelector = 'a[href^="mailto:"]';

    $('body').on('click', mailtoLinkSelector, trackClickEvent);

    function trackClickEvent(evt) {
      var $link = getLinkFromEvent(evt),
          options = {transport: 'beacon'},
          href = $link.attr('href'),
          linkText = $.trim($link.text());

      if (linkText) {
        options.label = linkText;
      }

      GOVUK.analytics.trackEvent('Mailto Link Clicked', href, options);
    }

    function getLinkFromEvent(evt) {
      var $target = $(evt.target);

      if (!$target.is('a')) {
        $target = $target.parents('a');
      }

      return $target;
    }
  }

  global.GOVUK = GOVUK;
})(window);

// Extension to monitor attempts to print pages.
(function (global) {
  "use strict";

  var GOVUK = global.GOVUK || {};

  GOVUK.analyticsPlugins = GOVUK.analyticsPlugins || {};

  GOVUK.analyticsPlugins.printIntent = function () {
    var printAttempt = (function () {
      GOVUK.analytics.trackEvent('Print Intent', document.location.pathname);
      GOVUK.analytics.trackPageview('/print' + document.location.pathname);
    });

    // Most browsers
    if (global.matchMedia) {
      var mediaQueryList = global.matchMedia('print'),
        mqlListenerCount = 0;
      mediaQueryList.addListener(function (mql) {
        if (!mql.matches && mqlListenerCount === 0) {
          printAttempt();
          mqlListenerCount++;
          // If we try and print again within 3 seconds, don't log it
          setTimeout(function () {
            mqlListenerCount = 0;
            // printing will be tracked again now
          }, 3000);
        }
      });
    }

    // IE < 10
    if (global.onafterprint) {
      global.onafterprint = printAttempt;
    }

  };

  global.GOVUK = GOVUK;
})(window);

(function(global) {
  "use strict";

  var GOVUK = global.GOVUK || {};
  GOVUK.Modules = GOVUK.Modules || {};

  GOVUK.Modules.AutoTrackEvent = function() {
    this.start = function(element) {
      var options = {nonInteraction: 1}, // automatic events shouldn't affect bounce rate
          category = element.data('track-category'),
          action = element.data('track-action'),
          label = element.data('track-label'),
          value = element.data('track-value');

      if (typeof label === "string") {
        options.label = label;
      }

      if (value || value === 0) {
        options.value = value;
      }

      if (GOVUK.analytics && GOVUK.analytics.trackEvent) {
        GOVUK.analytics.trackEvent(category, action, options);
      }
    }
  };

  global.GOVUK = GOVUK;
})(window);

/**
*    The Nomensa accessible media player is a flexible multimedia solution for websites and intranets.
*    The core player consists of JavaScript wrapper responsible for generating an accessible HTML toolbar
*    for interacting with a media player of your choice. We currently provide support for YouTube (default),
*    Vimeo and JWPlayer although it should be possible to integrate the player with almost any media player on
*    the web (provided a JavaScript api for the player in question is available).
*
*    Copyright (C) 2013  Nomensa Ltd
*
*    Version 2.1.2
*
*    This program is free software: you can redistribute it and/or modify
*    it under the terms of the GNU General Public License as published by
*    the Free Software Foundation, either version 3 of the License, or
*    (at your option) any later version.
*
*    This program is distributed in the hope that it will be useful,
*    but WITHOUT ANY WARRANTY; without even the implied warranty of
*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*    GNU General Public License for more details.
*
*    You should have received a copy of the GNU General Public License
*    along with this program.  If not, see <http://www.gnu.org/licenses/>.
**/
var swfobject=function(){var aq="undefined",aD="object",ab="Shockwave Flash",X="ShockwaveFlash.ShockwaveFlash",aE="application/x-shockwave-flash",ac="SWFObjectExprInst",ax="onreadystatechange",af=window,aL=document,aB=navigator,aa=false,Z=[aN],aG=[],ag=[],al=[],aJ,ad,ap,at,ak=false,aU=false,aH,an,aI=true,ah=function(){var a=typeof aL.getElementById!=aq&&typeof aL.getElementsByTagName!=aq&&typeof aL.createElement!=aq,e=aB.userAgent.toLowerCase(),c=aB.platform.toLowerCase(),h=c?/win/.test(c):/win/.test(e),j=c?/mac/.test(c):/mac/.test(e),g=/webkit/.test(e)?parseFloat(e.replace(/^.*webkit\/(\d+(\.\d+)?).*$/,"$1")):false,d=!+"\v1",f=[0,0,0],k=null;if(typeof aB.plugins!=aq&&typeof aB.plugins[ab]==aD){k=aB.plugins[ab].description;if(k&&!(typeof aB.mimeTypes!=aq&&aB.mimeTypes[aE]&&!aB.mimeTypes[aE].enabledPlugin)){aa=true;d=false;k=k.replace(/^.*\s+(\S+\s+\S+$)/,"$1");f[0]=parseInt(k.replace(/^(.*)\..*$/,"$1"),10);f[1]=parseInt(k.replace(/^.*\.(.*)\s.*$/,"$1"),10);f[2]=/[a-zA-Z]/.test(k)?parseInt(k.replace(/^.*[a-zA-Z]+(.*)$/,"$1"),10):0;}}else{if(typeof af.ActiveXObject!=aq){try{var i=new ActiveXObject(X);if(i){k=i.GetVariable("$version");if(k){d=true;k=k.split(" ")[1].split(",");f=[parseInt(k[0],10),parseInt(k[1],10),parseInt(k[2],10)];}}}catch(b){}}}return{w3:a,pv:f,wk:g,ie:d,win:h,mac:j};}(),aK=function(){if(!ah.w3){return;}if((typeof aL.readyState!=aq&&aL.readyState=="complete")||(typeof aL.readyState==aq&&(aL.getElementsByTagName("body")[0]||aL.body))){aP();}if(!ak){if(typeof aL.addEventListener!=aq){aL.addEventListener("DOMContentLoaded",aP,false);}if(ah.ie&&ah.win){aL.attachEvent(ax,function(){if(aL.readyState=="complete"){aL.detachEvent(ax,arguments.callee);aP();}});if(af==top){(function(){if(ak){return;}try{aL.documentElement.doScroll("left");}catch(a){setTimeout(arguments.callee,0);return;}aP();})();}}if(ah.wk){(function(){if(ak){return;}if(!/loaded|complete/.test(aL.readyState)){setTimeout(arguments.callee,0);return;}aP();})();}aC(aP);}}();function aP(){if(ak){return;}try{var b=aL.getElementsByTagName("body")[0].appendChild(ar("span"));b.parentNode.removeChild(b);}catch(a){return;}ak=true;var d=Z.length;for(var c=0;c<d;c++){Z[c]();}}function aj(a){if(ak){a();}else{Z[Z.length]=a;}}function aC(a){if(typeof af.addEventListener!=aq){af.addEventListener("load",a,false);}else{if(typeof aL.addEventListener!=aq){aL.addEventListener("load",a,false);}else{if(typeof af.attachEvent!=aq){aM(af,"onload",a);}else{if(typeof af.onload=="function"){var b=af.onload;af.onload=function(){b();a();};}else{af.onload=a;}}}}}function aN(){if(aa){Y();}else{am();}}function Y(){var d=aL.getElementsByTagName("body")[0];var b=ar(aD);b.setAttribute("type",aE);var a=d.appendChild(b);if(a){var c=0;(function(){if(typeof a.GetVariable!=aq){var e=a.GetVariable("$version");if(e){e=e.split(" ")[1].split(",");ah.pv=[parseInt(e[0],10),parseInt(e[1],10),parseInt(e[2],10)];}}else{if(c<10){c++;setTimeout(arguments.callee,10);return;}}d.removeChild(b);a=null;am();})();}else{am();}}function am(){var g=aG.length;if(g>0){for(var h=0;h<g;h++){var c=aG[h].id;var l=aG[h].callbackFn;var a={success:false,id:c};if(ah.pv[0]>0){var i=aS(c);if(i){if(ao(aG[h].swfVersion)&&!(ah.wk&&ah.wk<312)){ay(c,true);if(l){a.success=true;a.ref=av(c);l(a);}}else{if(aG[h].expressInstall&&au()){var e={};e.data=aG[h].expressInstall;e.width=i.getAttribute("width")||"0";e.height=i.getAttribute("height")||"0";if(i.getAttribute("class")){e.styleclass=i.getAttribute("class");}if(i.getAttribute("align")){e.align=i.getAttribute("align");}var f={};var d=i.getElementsByTagName("param");var k=d.length;for(var j=0;j<k;j++){if(d[j].getAttribute("name").toLowerCase()!="movie"){f[d[j].getAttribute("name")]=d[j].getAttribute("value");}}ae(e,f,c,l);}else{aF(i);if(l){l(a);}}}}}else{ay(c,true);if(l){var b=av(c);if(b&&typeof b.SetVariable!=aq){a.success=true;a.ref=b;}l(a);}}}}}function av(b){var d=null;var c=aS(b);if(c&&c.nodeName=="OBJECT"){if(typeof c.SetVariable!=aq){d=c;}else{var a=c.getElementsByTagName(aD)[0];if(a){d=a;}}}return d;}function au(){return !aU&&ao("6.0.65")&&(ah.win||ah.mac)&&!(ah.wk&&ah.wk<312);}function ae(f,d,h,e){aU=true;ap=e||null;at={success:false,id:h};var a=aS(h);if(a){if(a.nodeName=="OBJECT"){aJ=aO(a);ad=null;}else{aJ=a;ad=h;}f.id=ac;if(typeof f.width==aq||(!/%$/.test(f.width)&&parseInt(f.width,10)<310)){f.width="310";}if(typeof f.height==aq||(!/%$/.test(f.height)&&parseInt(f.height,10)<137)){f.height="137";}aL.title=aL.title.slice(0,47)+" - Flash Player Installation";var b=ah.ie&&ah.win?"ActiveX":"PlugIn",c="MMredirectURL="+af.location.toString().replace(/&/g,"%26")+"&MMplayerType="+b+"&MMdoctitle="+aL.title;if(typeof d.flashvars!=aq){d.flashvars+="&"+c;}else{d.flashvars=c;}if(ah.ie&&ah.win&&a.readyState!=4){var g=ar("div");h+="SWFObjectNew";g.setAttribute("id",h);a.parentNode.insertBefore(g,a);a.style.display="none";(function(){if(a.readyState==4){a.parentNode.removeChild(a);}else{setTimeout(arguments.callee,10);}})();}aA(f,d,h);}}function aF(a){if(ah.ie&&ah.win&&a.readyState!=4){var b=ar("div");a.parentNode.insertBefore(b,a);b.parentNode.replaceChild(aO(a),b);a.style.display="none";(function(){if(a.readyState==4){a.parentNode.removeChild(a);}else{setTimeout(arguments.callee,10);}})();}else{a.parentNode.replaceChild(aO(a),a);}}function aO(b){var d=ar("div");if(ah.win&&ah.ie){d.innerHTML=b.innerHTML;}else{var e=b.getElementsByTagName(aD)[0];if(e){var a=e.childNodes;if(a){var f=a.length;for(var c=0;c<f;c++){if(!(a[c].nodeType==1&&a[c].nodeName=="PARAM")&&!(a[c].nodeType==8)){d.appendChild(a[c].cloneNode(true));}}}}}return d;}function aA(e,g,c){var d,a=aS(c);if(ah.wk&&ah.wk<312){return d;}if(a){if(typeof e.id==aq){e.id=c;}if(ah.ie&&ah.win){var f="";for(var i in e){if(e[i]!=Object.prototype[i]){if(i.toLowerCase()=="data"){g.movie=e[i];}else{if(i.toLowerCase()=="styleclass"){f+=' class="'+e[i]+'"';}else{if(i.toLowerCase()!="classid"){f+=" "+i+'="'+e[i]+'"';}}}}}var h="";for(var j in g){if(g[j]!=Object.prototype[j]){h+='<param name="'+j+'" value="'+g[j]+'" />';}}a.outerHTML='<object classid="clsid:D27CDB6E-AE6D-11cf-96B8-444553540000"'+f+">"+h+"</object>";ag[ag.length]=e.id;d=aS(e.id);}else{var b=ar(aD);b.setAttribute("type",aE);for(var k in e){if(e[k]!=Object.prototype[k]){if(k.toLowerCase()=="styleclass"){b.setAttribute("class",e[k]);}else{if(k.toLowerCase()!="classid"){b.setAttribute(k,e[k]);}}}}for(var l in g){if(g[l]!=Object.prototype[l]&&l.toLowerCase()!="movie"){aQ(b,l,g[l]);}}a.parentNode.replaceChild(b,a);d=b;}}return d;}function aQ(b,d,c){var a=ar("param");a.setAttribute("name",d);a.setAttribute("value",c);b.appendChild(a);}function aw(a){var b=aS(a);if(b&&b.nodeName=="OBJECT"){if(ah.ie&&ah.win){b.style.display="none";(function(){if(b.readyState==4){aT(a);}else{setTimeout(arguments.callee,10);}})();}else{b.parentNode.removeChild(b);}}}function aT(a){var b=aS(a);if(b){for(var c in b){if(typeof b[c]=="function"){b[c]=null;}}b.parentNode.removeChild(b);}}function aS(a){var c=null;try{c=aL.getElementById(a);}catch(b){}return c;}function ar(a){return aL.createElement(a);}function aM(a,c,b){a.attachEvent(c,b);al[al.length]=[a,c,b];}function ao(a){var b=ah.pv,c=a.split(".");c[0]=parseInt(c[0],10);c[1]=parseInt(c[1],10)||0;c[2]=parseInt(c[2],10)||0;return(b[0]>c[0]||(b[0]==c[0]&&b[1]>c[1])||(b[0]==c[0]&&b[1]==c[1]&&b[2]>=c[2]))?true:false;}function az(b,f,a,c){if(ah.ie&&ah.mac){return;}var e=aL.getElementsByTagName("head")[0];if(!e){return;}var g=(a&&typeof a=="string")?a:"screen";if(c){aH=null;an=null;}if(!aH||an!=g){var d=ar("style");d.setAttribute("type","text/css");d.setAttribute("media",g);aH=e.appendChild(d);if(ah.ie&&ah.win&&typeof aL.styleSheets!=aq&&aL.styleSheets.length>0){aH=aL.styleSheets[aL.styleSheets.length-1];}an=g;}if(ah.ie&&ah.win){if(aH&&typeof aH.addRule==aD){aH.addRule(b,f);}}else{if(aH&&typeof aL.createTextNode!=aq){aH.appendChild(aL.createTextNode(b+" {"+f+"}"));}}}function ay(a,c){if(!aI){return;}var b=c?"visible":"hidden";if(ak&&aS(a)){aS(a).style.visibility=b;}else{az("#"+a,"visibility:"+b);}}function ai(b){var a=/[\\\"<>\.;]/;var c=a.exec(b)!=null;return c&&typeof encodeURIComponent!=aq?encodeURIComponent(b):b;}var aR=function(){if(ah.ie&&ah.win){window.attachEvent("onunload",function(){var a=al.length;for(var b=0;b<a;b++){al[b][0].detachEvent(al[b][1],al[b][2]);}var d=ag.length;for(var c=0;c<d;c++){aw(ag[c]);}for(var e in ah){ah[e]=null;}ah=null;for(var f in swfobject){swfobject[f]=null;}swfobject=null;});}}();return{registerObject:function(a,e,c,b){if(ah.w3&&a&&e){var d={};d.id=a;d.swfVersion=e;d.expressInstall=c;d.callbackFn=b;aG[aG.length]=d;ay(a,false);}else{if(b){b({success:false,id:a});}}},getObjectById:function(a){if(ah.w3){return av(a);}},embedSWF:function(k,e,h,f,c,a,b,i,g,j){var d={success:false,id:e};if(ah.w3&&!(ah.wk&&ah.wk<312)&&k&&e&&h&&f&&c){ay(e,false);aj(function(){h+="";f+="";var q={};if(g&&typeof g===aD){for(var o in g){q[o]=g[o];}}q.data=k;q.width=h;q.height=f;var n={};if(i&&typeof i===aD){for(var p in i){n[p]=i[p];}}if(b&&typeof b===aD){for(var l in b){if(typeof n.flashvars!=aq){n.flashvars+="&"+l+"="+b[l];}else{n.flashvars=l+"="+b[l];}}}if(ao(c)){var m=aA(q,n,e);if(q.id==e){ay(e,true);}d.success=true;d.ref=m;}else{if(a&&au()){q.data=a;ae(q,n,e,j);return;}else{ay(e,true);}}if(j){j(d);}});}else{if(j){j(d);}}},switchOffAutoHideShow:function(){aI=false;},ua:ah,getFlashPlayerVersion:function(){return{major:ah.pv[0],minor:ah.pv[1],release:ah.pv[2]};},hasFlashPlayerVersion:ao,createSWF:function(a,b,c){if(ah.w3){return aA(a,b,c);}else{return undefined;}},showExpressInstall:function(b,a,d,c){if(ah.w3&&au()){ae(b,a,d,c);}},removeSWF:function(a){if(ah.w3){aw(a);}},createCSS:function(b,a,c,d){if(ah.w3){az(b,a,c,d);}},addDomLoadEvent:aj,addLoadEvent:aC,getQueryParamValue:function(b){var a=aL.location.search||aL.location.hash;if(a){if(/\?/.test(a)){a=a.split("?")[1];}if(b==null){return ai(a);}var c=a.split("&");for(var d=0;d<c.length;d++){if(c[d].substring(0,c[d].indexOf("="))==b){return ai(c[d].substring((c[d].indexOf("=")+1)));}}}return"";},expressInstallCallback:function(){if(aU){var a=aS(ac);if(a&&aJ){a.parentNode.replaceChild(aJ,a);if(ad){ay(ad,true);if(ah.ie&&ah.win){aJ.style.display="block";}}if(ap){ap(at);}}aU=false;}}};}();(function(d){d.NOMENSA=d.NOMENSA||{};var a,c,b;d.NOMENSA.uaMatch=function(f){f=f.toLowerCase();var e=/(webkit)[ \/]([\w.]+)/.exec(f)||/(opera)(?:.*version|)[ \/]([\w.]+)/.exec(f)||/(msie) ([\w.]+)/.exec(f)||f.indexOf("compatible")<0&&/(mozilla)(?:.*? rv:([\w.]+)|)/.exec(f)||[];return{browser:e[1]||"",version:e[2]||"0"};};a=d.NOMENSA.uaMatch(d.navigator.userAgent);c={};if(a.browser){c[a.browser]=true;c.version=a.version;}d.NOMENSA.browser=c;})(window);window.NOMENSA=window.NOMENSA||{};window.NOMENSA.player=window.NOMENSA.player||{};window.NOMENSA.player.YoutubePlayer=function(a){this.config=a;this.config.playerVars={controls:0,showinfo:0,origin:window.location.protocol+"//"+window.location.hostname,rel:0};};window.NOMENSA.player.YoutubePlayer.apiLoaded=false;window.NOMENSA.player.YoutubePlayer.prototype={getYTOptions:function(){var b=this,a={height:this.config.flashHeight,width:this.config.flashWidth,videoId:this.config.media,events:{onReady:function(c){b.$html.find("iframe").attr({id:b.config.id,role:"presentation"});b.onPlayerReady(c);},onStateChange:function(c){b.onPlayerStateChange(c.data);}}};a.playerVars=this.config.playerVars;if(this.config.repeat){a.playerVars.playlist=this.config.media;}return a;},init:function(){if(typeof window.postMessage!=="undefined"){return function(d){var a=document.createElement("script"),b=document.getElementsByTagName("script")[0],c=this;this.$html=this.assembleHTML();if(this.config.captions){this.getCaptions();}d.html(this.$html);window.NOMENSA.player.PlayerDaemon.addPlayer(this);if(!window.NOMENSA.player.YoutubePlayer.apiLoaded){if(typeof window.onYouTubeIframeAPIReady==="undefined"){window.onYouTubeIframeAPIReady=function(){window.NOMENSA.player.PlayerDaemon.map(function(e){if(typeof e.getYTOptions!=="undefined"){e.player=new YT.Player("player-"+e.config.id,e.getYTOptions());}});window.NOMENSA.player.YoutubePlayer.apiLoaded=true;};a.src="//www.youtube.com/iframe_api";b.parentNode.insertBefore(a,b);}}else{this.player=YT.Player("player-"+player.config.id,getOptions(player));}};}else{return function(b){var a=this;this.$html=this.assembleHTML();if(this.config.captions){this.getCaptions();}b.html(this.$html);window.NOMENSA.player.PlayerDaemon.addPlayer(this);window.NOMENSA.player.stateHandlers[this.config.id]=function(d){var c=window.NOMENSA.player.PlayerDaemon.getPlayer(a.config.id);c.onPlayerStateChange(d);};window.onYouTubePlayerReady=function(c){var d=window.NOMENSA.player.PlayerDaemon.getPlayer(c);var e=document.getElementById(d.config.id);d.player=e;d.cue();d.getPlayer().addEventListener("onStateChange","window.NOMENSA.player.stateHandlers."+a.config.id);d.onPlayerReady();};};}}(),state:{ended:0,playing:1,paused:2,unstarted:-1},onPlayerReady:(function(){var b=[],a;return function(d){var c=b.length;if(typeof d==="function"){b.push(d);}else{if(c===0){return false;}for(a=0;a<c;a++){b[a].apply(this,arguments);}}};}()),onPlayerStateChange:function(a){if(a==1){this.play();if(this.config.buttons.toggle){this.$html.find(".play").removeClass("play").addClass("pause").text("Pause");}}else{if(this.config.repeat&&(a==0)){this.play();}}},getFlashVars:function(){var a={controlbar:"none",file:this.config.media};if(this.config.image!=""){a.image=this.config.image;}if(this.config.repeat){a.repeat=this.config.repeat;}return a;},getFlashParams:function(){return{allowScriptAccess:"always",wmode:"transparent"};},generateFlashPlayer:function(c){var g=this;var a=this.getFlashVars();var f=this.getFlashParams();var h={id:this.config.id,name:this.config.id};var e=$("<"+this.config.flashContainer+" />").attr("id","player-"+this.config.id).addClass("flashReplace").html('This content requires Macromedia Flash Player. You can <a href="http://get.adobe.com/flashplayer/">install or upgrade the Adobe Flash Player here</a>.');var d=$("<span />").addClass("video");var b=this.getURL();setTimeout(function(){swfobject.embedSWF(b,e.attr("id"),g.config.flashWidth,g.config.flashHeight,"9.0.115",null,a,f,h,g.config.swfCallback);if(window.NOMENSA.browser.mozilla&&(parseInt(window.NOMENSA.browser.version,10)>=2)){g.$html.find("object").attr("tabindex","-1");}},0);c.append(d.append(e));return c;},generateVideoPlayer:function(b){if(typeof window.postMessage==="undefined"){return this.generateFlashPlayer(b);}else{var a=$("<"+this.config.flashContainer+" />").attr("id","player-"+this.config.id);var c=$("<span />").addClass("video");b.append(c.append(a));return b;}},getPlayer:function(){return this.player;},is_html5:false,play:function(){this.player.playVideo();this.setSliderTimeout();if(this.config.captionsOn&&this.captions){this.setCaptionTimeout();}},pause:function(){this.player.pauseVideo();this.clearSliderTimeout();if(this.config.captionsOn&&this.captions){this.clearCaptionTimeout();}},ffwd:function(){var b=this.getCurrentTime()+this.config.playerSkip,a=this.getDuration();if(b>a){b=a;}this.seek(b);},rewd:function(){var a=this.getCurrentTime()-this.config.playerSkip;if(a<0){a=0;}this.seek(a);},mute:function(){var a=this.$html.find("button.mute");if(this.player.isMuted()){this.player.unMute();if(a.hasClass("muted")){a.removeClass("muted");}}else{this.player.mute();a.addClass("muted");}},volup:function(){var a=this.player.getVolume();if(a>=100){a=100;}else{a=a+this.config.volumeStep;}this.player.setVolume(a);this.updateVolume(a);},voldwn:function(){var a=this.player.getVolume();if(a<=0){a=0;}else{a=a-this.config.volumeStep;}this.player.setVolume(a);this.updateVolume(a);},getDuration:function(){return this.player.getDuration();},getCurrentTime:function(){return this.player.getCurrentTime();},getBytesLoaded:function(){return this.player.getVideoBytesLoaded();},getBytesTotal:function(){return this.player.getVideoBytesTotal();},seek:function(a){this.player.seekTo(a,true);if(this.config.captionsOn&&this.captions){this.$html.find(".caption").remove();this.clearCaptionTimeout();this.setCaptionTimeout();this.getPreviousCaption();}},cue:function(){this.player.cueVideoById(this.config.media);},toggleCaptions:function(){var a=this;var b=this.$html.find(".captions");if(b.hasClass("captions-off")){b.removeClass("captions-off").addClass("captions-on");a.getPreviousCaption();a.setCaptionTimeout();a.config.captionsOn=true;}else{b.removeClass("captions-on").addClass("captions-off");a.clearCaptionTimeout();a.$html.find(".caption").remove();a.config.captionsOn=false;}}};window.NOMENSA=window.NOMENSA||{};window.NOMENSA.player=window.NOMENSA.player||{};window.NOMENSA.player.MediaplayerDecorator=function(a){var b=a;this.config=b.config;this.player=b.player;this.state=b.state;for(var c in b){if(typeof b[c]==="function"){this[c]=(function(d){return function(){return b[d].apply(this,arguments);};}(c));}}};window.NOMENSA.player.MediaplayerDecorator.prototype.generatePlayerContainer=function(){var a=$("<"+this.config.playerContainer+" />").css(this.config.playerStyles).addClass("player-container");if(window.NOMENSA.browser.msie){a.addClass("player-container-ie player-container-ie-"+window.NOMENSA.browser.version.substring(0,1));}return a;};window.NOMENSA.player.MediaplayerDecorator.prototype.assembleHTML=function(){var a=this.generatePlayerContainer();var c=this.generateVideoPlayer(a);var b=c.append(this.getControls());return b;};window.NOMENSA.player.MediaplayerDecorator.prototype.getURL=function(){return[this.config.url,this.config.id].join("");};window.NOMENSA.player.MediaplayerDecorator.prototype.createButton=function(d,b){var a=0;var e=[d,this.config.id].join("-");var c=$("<button />").append(b).addClass(d).attr({title:d,id:e}).addClass("ui-corner-all ui-state-default").hover(function(){$(this).addClass("ui-state-hover");},function(){$(this).removeClass("ui-state-hover");}).focus(function(){$(this).addClass("ui-state-focus");}).blur(function(){$(this).removeClass("ui-state-focus");}).click(function(f){f.preventDefault();});return c;};window.NOMENSA.player.MediaplayerDecorator.prototype.getFuncControls=function(){var l=this;var j=$("<div>");j[0].className="player-controls";var g=[];if(l.config.buttons.toggle){var a=l.createButton("play","Play").attr({"aria-live":"assertive"}).click(function(){if($(this).hasClass("play")){$(this).removeClass("play").addClass("pause").attr({title:"Pause",id:"pause-"+l.config.id}).text("Pause");l.play();}else{$(this).removeClass("pause").addClass("play").attr({title:"Play",id:"play-"+l.config.id}).text("Play");l.pause();}});g.push(a);}else{var c=l.createButton("play","Play").click(function(){l.play();});var k=l.createButton("pause","Pause").click(function(){l.pause();});g.push(c);g.push(k);}if(l.config.buttons.rewind){var f=l.createButton("rewind","Rewind").click(function(){l.rewd();});g.push(f);}if(l.config.buttons.forward){var h=l.createButton("forward","Forward").click(function(){l.ffwd();});g.push(h);}if(l.config.captions){var b=l.createButton("captions","Captions").click(function(){l.toggleCaptions();});var d=(l.config.captionsOn==true)?"captions-on":"captions-off";b.addClass(d);g.push(b);}for(var e=0;e<g.length;e=e+1){j[0].appendChild(g[e][0]);}return j;};window.NOMENSA.player.MediaplayerDecorator.prototype.getVolControls=function(){var c=this;var g=$("<div>").addClass("volume-controls");var b=c.createButton("mute","Mute").click(function(){c.mute();});var h=c.createButton("vol-up",'+<span class="ui-helper-hidden-accessible"> Volume Up</span>').click(function(){c.volup();});var e=c.createButton("vol-down",'-<span class="ui-helper-hidden-accessible"> Volume Down</span>').click(function(){c.voldwn();});var f=$("<span />").attr({id:"vol-"+c.config.id,"class":"vol-display"}).text("100%");var a=[b,e,h,f];for(var d=0;d<a.length;d=d+1){g[0].appendChild(a[d][0]);}return g;};window.NOMENSA.player.MediaplayerDecorator.prototype.getSliderBar=function(){var c=$("<span />").addClass("ui-helper-hidden-accessible").html("<p>The timeline slider below uses WAI ARIA. Please use the documentation for your screen reader to find out more.</p>");var a=$("<span />").addClass("current-time").attr({id:"current-"+this.config.id}).text("00:00:00");var g=this.getSlider();var f=$("<span />").addClass("duration-time").attr({id:"duration-"+this.config.id}).text("00:00:00");var e=$("<div />").addClass("timer-bar").append(c);var d=[a,g,f];for(var b=0;b<d.length;b=b+1){e[0].appendChild(d[b][0]);}return e;};window.NOMENSA.player.MediaplayerDecorator.prototype.getSlider=function(){var d=this;var a=$("<span />").attr("id","slider-"+this.config.id).slider({orientation:"horizontal",change:function(f,g){var e=g.value;var h=(e/100)*d.getDuration();d.seek(h);}});a.find("a.ui-slider-handle").attr({role:"slider","aria-valuemin":"0","aria-valuemax":"100","aria-valuenow":"0","aria-valuetext":"0 percent",title:"Slider Control"});var c=$("<span />").addClass("progress-bar").attr({id:"progress-bar-"+this.config.id,tabindex:"-1"}).addClass("ui-progressbar-value ui-widget-header ui-corner-left").css({width:"0%",height:"95%"});var b=$("<span />").attr({id:"loaded-bar-"+this.config.id,tabindex:"-1"}).addClass("loaded-bar ui-progressbar-value ui-widget-header ui-corner-left").css({height:"95%",width:"0%"});return a.append(c,b);};window.NOMENSA.player.MediaplayerDecorator.prototype.setSliderTimeout=function(){var a=this;if(a.sliderInterval==undefined){a.sliderInterval=setInterval(function(){a.updateSlider();},a.config.sliderTimeout);}};window.NOMENSA.player.MediaplayerDecorator.prototype.clearSliderTimeout=function(){var a=this;if(a.sliderInterval!=undefined){a.sliderInterval=clearInterval(a.sliderInterval);}};window.NOMENSA.player.MediaplayerDecorator.prototype.updateSlider=function(){var c=(typeof(this.duration)!="undefined")?this.duration:this.getDuration();var a=(typeof(this.duration_found)=="boolean")?this.duration_found:false;var d=this.getCurrentTime();var b=0;if(c>0){b=(d/c)*100;b=parseInt(b,10);}else{c=0;}if(!a){$("#duration-"+this.config.id).html(this.formatTime(parseInt(c,10)));this.duration_found=true;}$("#slider-"+this.config.id).find("a.ui-slider-handle").attr({"aria-valuenow":b,"aria-valuetext":b.toString()+" percent"}).css("left",b.toString()+"%");$("#progress-bar-"+this.config.id).attr({"aria-valuenow":b,"aria-valuetext":b.toString()+" percent"}).css("width",b.toString()+"%");this.updateLoaderBar();this.updateTime(d);};window.NOMENSA.player.MediaplayerDecorator.prototype.updateLoaderBar=function(){var a=(this.getBytesLoaded()/this.getBytesTotal())*100;a=parseInt(a,10);if(!isFinite(a)){a=0;}$("#loaded-bar-"+this.config.id).attr({"aria-valuetext":a.toString()+" percent","aria-valuenow":a}).css("width",a.toString()+"%");};window.NOMENSA.player.MediaplayerDecorator.prototype.formatTime=function(e){var a=0;var d=0;var f=0;if(e>=60){d=parseInt(e/60,10);f=e-(d*60);if(d>=60){a=parseInt(d/60,10);d-=parseInt(a*60,10);}}else{f=e;}var c=[a,d,f];for(var b=0;b<c.length;b=b+1){c[b]=(c[b]<10)?"0"+c[b].toString():c[b].toString();}return c.join(":");};window.NOMENSA.player.MediaplayerDecorator.prototype.updateTime=function(b){var a=this.formatTime(parseInt(b,10));this.$html.find("#current-"+this.config.id).html(a);};window.NOMENSA.player.MediaplayerDecorator.prototype.getControls=function(){var a=$("<span />").addClass("ui-corner-bottom").addClass("control-bar");var d=$("<a />").attr("href","http://www.nomensa.com?ref=logo").html("Accessible Media Player by Nomensa").addClass("logo");a.append(d);var b=this.getFuncControls();var e=this.getVolControls();var g=this.getSliderBar();var f=[b,e,g];for(var c=0;c<f.length;c=c+1){a[0].appendChild(f[c][0]);}return a;};window.NOMENSA.player.MediaplayerDecorator.prototype.updateVolume=function(b){$("#vol-"+this.config.id).text(b.toString()+"%");var a=this.$html.find("button.mute");if(b==0){a.addClass("muted");}else{if(a.hasClass("muted")){a.removeClass("muted");}}};window.NOMENSA.player.MediaplayerDecorator.prototype.getCaptions=function(){var b=this;if(b.config.captions){var a=[];$.ajax({url:b.config.captions,success:function(c){if($(c).find("p").length>0){b.captions=$(c).find("p");}}});}};window.NOMENSA.player.MediaplayerDecorator.prototype.toggleCaptions=function(){var a=this;var b=this.$html.find(".captions");if(b.hasClass("captions-off")){b.removeClass("captions-off").addClass("captions-on");a.getPreviousCaption();a.setCaptionTimeout();a.config.captionsOn=true;}else{b.removeClass("captions-on").addClass("captions-off");a.clearCaptionTimeout();a.$html.find(".caption").remove();a.config.captionsOn=false;}};window.NOMENSA.player.MediaplayerDecorator.prototype.syncCaptions=function(){var a;if(this.captions){var b=this.getCurrentTime();b=this.formatTime(parseInt(b,10));a=this.captions.filter('[begin="'+b+'"]');if(a.length==1){this.insertCaption(a);}}};window.NOMENSA.player.MediaplayerDecorator.prototype.insertCaption=function(a){if(this.$html.find(".caption").length==1){this.$html.find(".caption").text(a.text());}else{var b=$("<div>").text(a.text());b[0].className="caption";this.$html.find(".video").prepend(b);}};window.NOMENSA.player.MediaplayerDecorator.prototype.getPreviousCaption=function(c){var a;if(c==undefined){c=this.getCurrentTime();}var b=this.formatTime(parseInt(c,10));if(this.captions){a=this.captions.filter('[begin="'+b+'"]');while((a.length!=1)&&(c>0)){c--;b=this.formatTime(parseInt(c,10));a=this.captions.filter('[begin="'+b+'"]');}if(a.length==1){this.insertCaption(a);}}};window.NOMENSA.player.MediaplayerDecorator.prototype.destroyPlayerInstance=function(){return false;};window.NOMENSA.player.MediaplayerDecorator.prototype.destroy=function(){this.clearSliderTimeout();this.clearCaptionTimeout();this.destroyPlayerInstance();this.$html.remove();};window.NOMENSA.player.MediaplayerDecorator.prototype.setCaptionTimeout=function(){var a=this;if(a.captionInterval==undefined){a.captionInterval=setInterval(function(){a.syncCaptions();},500);}};window.NOMENSA.player.MediaplayerDecorator.prototype.clearCaptionTimeout=function(){if(this.captionInterval!=undefined){this.captionInterval=clearInterval(this.captionInterval);}};window.NOMENSA=window.NOMENSA||{};window.NOMENSA.player=window.NOMENSA.player||{};jQuery(function(a){a(window).resize(function(){a(".player-container").each(function(){if(a(this).width()>580){a(this).addClass("player-wide");}else{a(this).removeClass("player-wide");}});});});if(typeof window.postMessage==="undefined"){window.NOMENSA.player.stateHandlers={};}window.NOMENSA.player.PlayerManager=function(){var a={};this.getPlayer=function(b){if(a[b]!=undefined){return a[b];}return null;};this.addPlayer=function(b){a[b.config.id]=b;return true;};this.removePlayer=function(b){if(a[b]!=undefined){a[b].destroy();delete a[b];}};this.map=function(c){var b;for(b in a){c(a[b]);}};};window.NOMENSA.player.PlayerDaemon=new window.NOMENSA.player.PlayerManager();var html5_methods={play:function(){this.player.play();this.setSliderTimeout();if(this.config.captionsOn&&this.captions){this.setCaptionTimeout();}},pause:function(){this.player.pause();this.clearSliderTimeout();if(this.config.captionsOn&&this.captions){this.clearCaptionTimeout();}},ffwd:function(){var a=this.getCurrentTime()+this.config.playerSkip;this.seek(a);},rewd:function(){var a=this.getCurrentTime()-this.config.playerSkip;if(a<0){a=0;}this.seek(a);},mute:function(){var a=this.$html.find("button.mute");if(this.player.muted){this.player.muted=false;if(a.hasClass("muted")){a.removeClass("muted");}}else{this.player.muted=true;a.addClass("muted");}},volup:function(){var a=this.player.volume*100;if(a<(100-this.config.volumeStep)){a+=this.config.volumeStep;}else{a=100;}this.player.volume=(a/100);this.updateVolume(Math.round(a));},voldwn:function(){var a=this.player.volume*100;if(a>this.config.volumeStep){a-=this.config.volumeStep;}else{a=0;}this.player.volume=(a/100);this.updateVolume(Math.round(a));},getDuration:function(){return this.player.duration;},getCurrentTime:function(){return this.player.currentTime;},getBytesLoaded:function(){return this.player.buffered.end(0);},getBytesTotal:function(){return this.player.duration;},seek:function(a){this.player.currentTime=a;},cue:function(){return;}};(function(a){a.fn.player=function(k,f){var e={id:"media_player",url:window.location.protocol+"//www.youtube.com/apiplayer?enablejsapi=1&version=3&playerapiid=",media:"8LiQ-bLJaM4",repeat:false,captions:null,captionsOn:true,flashWidth:"100%",flashHeight:"300px",playerStyles:{height:"100%",width:"100%"},sliderTimeout:350,flashContainer:"span",playerContainer:"span",image:"",playerSkip:10,volumeStep:10,buttons:{forward:true,rewind:true,toggle:true},logoURL:"http://www.nomensa.com?ref=logo",useHtml5:true,swfCallback:null};var c=a.extend(true,{},e,k);var i=function(p){var s=p.config.media,r,o,q,n,m,l;n=function(t){r=document.createElement(t.container);if(r.canPlayType!=undefined){q=r.canPlayType(t.mimetype);if((q.toLowerCase()=="maybe")||(q.toLowerCase()=="probably")){return true;}}};if(typeof s==="string"){o=g(s);if(n(o)){o.src=s;return o;}}if((s instanceof Array)&&(typeof s.push!=="undefined")){for(m=0,l=s.length;m<l;m++){o=g(s[m]);if(n(o)){o.src=s[m];return o;}}}return false;};var h=function(n){var m="";var l="video";switch(n){case"mp4":m='video/mp4; codecs="avc1.42E01E, mp4a.40.2"';break;case"m4v":m='video/mp4; codecs="avc1.42E01E, mp4a.40.2"';break;case"ogg":m='video/ogg; codecs="theora, vorbis"';break;case"ogv":m='video/ogg; codecs="theora, vorbis"';break;case"webm":m='video/webm; codecs="vp8, vorbis"';break;case"mp3":m="audio/mpeg";l="audio";break;}return{mimetype:m,container:l};};var g=function(o){var m=o.lastIndexOf(".");if(m!=-1){var l=o.substring(m+1);var n=h(l);return n;}return null;};var b=function(){if(window.NOMENSA.browser.mozilla){return(parseInt(window.NOMENSA.browser.version,10)>=2)?true:false;}return false;};var d={generatePlayerContainer:function(){var l=a("<"+this.config.playerContainer+" />").css(this.config.playerStyles).addClass("player-container");if(window.NOMENSA.browser.msie){l.addClass("player-container-ie player-container-ie-"+window.NOMENSA.browser.version.substring(0,1));}return l;},getFlashVars:function(){var l={controlbar:"none",file:this.config.media};if(this.config.image!=""){l.image=this.config.image;}if(this.config.repeat){l.repeat=this.config.repeat;}return l;},getFlashParams:function(){return{allowScriptAccess:"always",wmode:"transparent"};},getURL:function(){return[this.config.url,this.config.id].join("");},generateFlashPlayer:function(n){var r=this;var l=this.getFlashVars();var q=this.getFlashParams();var s={id:this.config.id,name:this.config.id};var p=a("<"+this.config.flashContainer+" />").attr("id","player-"+this.config.id).addClass("flashReplace").html('This content requires Macromedia Flash Player. You can <a href="http://get.adobe.com/flashplayer/">install or upgrade the Adobe Flash Player here</a>.');var o=a("<span />").addClass("video");var m=this.getURL();setTimeout(function(){swfobject.embedSWF(m,p.attr("id"),r.config.flashWidth,r.config.flashHeight,"9.0.115",null,l,q,s,r.config.swfCallback);if(b()){r.$html.find("object").attr("tabindex","-1");}},0);n.append(o.append(p));return n;},generateHTML5Player:function(m,p,o){var n=a("<span />");n[0].className="video";var l=a("<"+p+" />").attr({id:this.config.id,src:this.config.media,type:o}).css({width:"100%",height:"50%"});if(a.trim(this.config.image)!=""){l.attr({poster:a.trim(this.config.image)});}return m.append(n.append(l));},createButton:function(o,m){var l=0;var p=[o,this.config.id].join("-");var n=a("<button />").append(m).addClass(o).attr({title:o,id:p}).addClass("ui-corner-all ui-state-default").hover(function(){a(this).addClass("ui-state-hover");},function(){a(this).removeClass("ui-state-hover");}).focus(function(){a(this).addClass("ui-state-focus");}).blur(function(){a(this).removeClass("ui-state-focus");}).click(function(q){q.preventDefault();});return n;},getFuncControls:function(){var v=this;var t=a("<div>");t[0].className="player-controls";var r=[];if(v.config.buttons.toggle){var l=v.createButton("play","Play").attr({"aria-live":"assertive"}).click(function(){if(a(this).hasClass("play")){a(this).removeClass("play").addClass("pause").attr({title:"Pause",id:"pause-"+v.config.id}).text("Pause");v.play();}else{a(this).removeClass("pause").addClass("play").attr({title:"Play",id:"play-"+v.config.id}).text("Play");v.pause();}});r.push(l);}else{var n=v.createButton("play","Play").click(function(){v.play();});var u=v.createButton("pause","Pause").click(function(){v.pause();});r.push(n);r.push(u);}if(v.config.buttons.rewind){var q=v.createButton("rewind","Rewind").click(function(){v.rewd();});r.push(q);}if(v.config.buttons.forward){var s=v.createButton("forward","Forward").click(function(){v.ffwd();});r.push(s);}if(v.config.captions){var m=v.createButton("captions","Captions").click(function(){v.toggleCaptions();});var o=(v.config.captionsOn==true)?"captions-on":"captions-off";m.addClass(o);r.push(m);}var p;for(p=0;p<r.length;p=p+1){t[0].appendChild(r[p][0]);}return t;},getVolControls:function(){var n=this;var r=a("<div>").addClass("volume-controls");var m=n.createButton("mute","Mute").click(function(){n.mute();});var s=n.createButton("vol-up",'+<span class="ui-helper-hidden-accessible"> Volume Up</span>').click(function(){n.volup();});var p=n.createButton("vol-down",'-<span class="ui-helper-hidden-accessible"> Volume Down</span>').click(function(){n.voldwn();});var q=a("<span />").attr({id:"vol-"+n.config.id,"class":"vol-display"}).text("100%");var l=[m,p,s,q];var o;for(o=0;o<l.length;o=o+1){r[0].appendChild(l[o][0]);}return r;},getSliderBar:function(){var n=a("<span />").addClass("ui-helper-hidden-accessible").html("<p>The timeline slider below uses WAI ARIA. Please use the documentation for your screen reader to find out more.</p>");var l=a("<span />").addClass("current-time").attr({id:"current-"+this.config.id}).text("00:00:00");var r=this.getSlider();var q=a("<span />").addClass("duration-time").attr({id:"duration-"+this.config.id}).text("00:00:00");var p=a("<div />").addClass("timer-bar").append(n);var o=[l,r,q];var m;for(m=0;m<o.length;m=m+1){p[0].appendChild(o[m][0]);}return p;},getSlider:function(){var o=this;var l=a("<span />").attr("id","slider-"+this.config.id).slider({orientation:"horizontal",change:function(q,r){var p=r.value;var s=(p/100)*o.getDuration();o.seek(s);}});l.find("a.ui-slider-handle").attr({role:"slider","aria-valuemin":"0","aria-valuemax":"100","aria-valuenow":"0","aria-valuetext":"0 percent",title:"Slider Control"});var n=a("<span />").addClass("progress-bar").attr({id:"progress-bar-"+this.config.id,tabindex:"-1"}).addClass("ui-progressbar-value ui-widget-header ui-corner-left").css({width:"0%",height:"95%"});var m=a("<span />").attr({id:"loaded-bar-"+this.config.id,tabindex:"-1"}).addClass("loaded-bar ui-progressbar-value ui-widget-header ui-corner-left").css({height:"95%",width:"0%"});return l.append(n,m);},setSliderTimeout:function(){var l=this;if(l.sliderInterval==undefined){l.sliderInterval=setInterval(function(){l.updateSlider();},l.config.sliderTimeout);}},clearSliderTimeout:function(){var l=this;if(l.sliderInterval!=undefined){l.sliderInterval=clearInterval(l.sliderInterval);}},updateSlider:function(){var n=(typeof(this.duration)!="undefined")?this.duration:this.getDuration();var l=(typeof(this.duration_found)=="boolean")?this.duration_found:false;var o=this.getCurrentTime();var m=0;if(n>0){m=(o/n)*100;m=parseInt(m,10);}else{n=0;}if(!l){a("#duration-"+this.config.id).html(this.formatTime(parseInt(n,10)));this.duration_found=true;}a("#slider-"+this.config.id).find("a.ui-slider-handle").attr({"aria-valuenow":m,"aria-valuetext":m.toString()+" percent"}).css("left",m.toString()+"%");a("#progress-bar-"+this.config.id).attr({"aria-valuenow":m,"aria-valuetext":m.toString()+" percent"}).css("width",m.toString()+"%");this.updateLoaderBar();this.updateTime(o);},updateLoaderBar:function(){var l=(this.getBytesLoaded()/this.getBytesTotal())*100;l=parseInt(l,10);if(!isFinite(l)){l=0;}a("#loaded-bar-"+this.config.id).attr({"aria-valuetext":l.toString()+" percent","aria-valuenow":l}).css("width",l.toString()+"%");},formatTime:function(p){var l=0;var o=0;var q=0;if(p>=60){o=parseInt(p/60,10);q=p-(o*60);if(o>=60){l=parseInt(o/60,10);o-=parseInt(l*60,10);}}else{q=p;}var n=[l,o,q];var m;for(m=0;m<n.length;m=m+1){n[m]=(n[m]<10)?"0"+n[m].toString():n[m].toString();}return n.join(":");},updateTime:function(m){var l=this.formatTime(parseInt(m,10));this.$html.find("#current-"+this.config.id).html(l);},getControls:function(){var l=a("<span />").addClass("ui-corner-bottom").addClass("control-bar");var o=a("<a />").attr("href","http://www.nomensa.com?ref=logo").html("Accessible Media Player by Nomensa").addClass("logo");l.append(o);var m=this.getFuncControls();var p=this.getVolControls();var r=this.getSliderBar();var q=[m,p,r];var n;for(n=0;n<q.length;n=n+1){l[0].appendChild(q[n][0]);}return l;},assembleHTML:function(){var l=this.generatePlayerContainer();var n=this.generateFlashPlayer(l);var m=n.append(this.getControls());return m;},assembleHTML5:function(p,o){var l=this.generatePlayerContainer();var n=this.generateHTML5Player(l,p,o);var m=n.append(this.getControls());return m;},updateVolume:function(m){a("#vol-"+this.config.id).text(m.toString()+"%");var l=this.$html.find("button.mute");if(m==0){l.addClass("muted");}else{if(l.hasClass("muted")){l.removeClass("muted");}}},getCaptions:function(){var m=this;if(m.config.captions){var l=[];a.ajax({url:m.config.captions,success:function(n){if(a(n).find("p").length>0){m.captions=a(n).find("p");}}});}},syncCaptions:function(){var l;if(this.captions){var m=this.getCurrentTime();m=this.formatTime(parseInt(m,10));l=this.captions.filter('[begin="'+m+'"]');if(l.length==1){this.insertCaption(l);}}},insertCaption:function(l){if(this.$html.find(".caption").length==1){this.$html.find(".caption").text(l.text());}else{var m=a("<div>").text(l.text());m[0].className="caption";this.$html.find(".video").prepend(m);}},getPreviousCaption:function(n){var l;if(n==undefined){n=this.getCurrentTime();}var m=this.formatTime(parseInt(n,10));if(this.captions){l=this.captions.filter('[begin="'+m+'"]');while((l.length!=1)&&(n>0)){n--;m=this.formatTime(parseInt(n,10));l=this.captions.filter('[begin="'+m+'"]');}if(l.length==1){this.insertCaption(l);}}},destroyPlayerInstance:function(){return false;},destroy:function(){this.clearSliderTimeout();this.clearCaptionTimeout();this.destroyPlayerInstance();this.$html.remove();},setCaptionTimeout:function(){var l=this;if(l.captionInterval==undefined){l.captionInterval=setInterval(function(){l.syncCaptions();},500);}},clearCaptionTimeout:function(){if(this.captionInterval!=undefined){this.captionInterval=clearInterval(this.captionInterval);}},play:function(){this.player.playVideo();this.setSliderTimeout();if(this.config.captionsOn&&this.captions){this.setCaptionTimeout();}},pause:function(){this.player.pauseVideo();this.clearSliderTimeout();if(this.config.captionsOn&&this.captions){this.clearCaptionTimeout();}},ffwd:function(){var l=this.getCurrentTime()+this.config.playerSkip;this.seek(l);},rewd:function(){var l=this.getCurrentTime()-this.config.playerSkip;if(l<0){l=0;}this.seek(l);},mute:function(){var l=this.$html.find("button.mute");if(this.player.isMuted()){this.player.unMute();if(l.hasClass("muted")){l.removeClass("muted");}}else{this.player.mute();l.addClass("muted");}},volup:function(){var l=this.player.getVolume();if(l<(100-this.config.volumeStep)){l+=this.config.volumeStep;}else{l=100;}this.player.setVolume(l);this.updateVolume(l);},voldwn:function(){var l=this.player.getVolume();if(l>this.config.volumeStep){l-=this.config.volumeStep;}else{l=0;}this.player.setVolume(l);this.updateVolume(l);},getDuration:function(){return this.player.getDuration();},getCurrentTime:function(){return this.player.getCurrentTime();},getBytesLoaded:function(){return this.player.getVideoBytesLoaded();},getBytesTotal:function(){return this.player.getVideoBytesTotal();},seek:function(l){this.player.seekTo(l);if(this.config.captionsOn&&this.captions){this.$html.find(".caption").remove();this.clearCaptionTimeout();this.setCaptionTimeout();this.getPreviousCaption();}},cue:function(){this.player.cueVideoById(this.config.media);},toggleCaptions:function(){var l=this;var m=this.$html.find(".captions");if(m.hasClass("captions-off")){m.removeClass("captions-off").addClass("captions-on");l.getPreviousCaption();l.setCaptionTimeout();l.config.captionsOn=true;}else{m.removeClass("captions-on").addClass("captions-off");l.clearCaptionTimeout();l.$html.find(".caption").remove();l.config.captionsOn=false;}}};function j(l){this.config=c;a.extend(true,this,d,f);this.is_html5=false;var m=i(this);if(m&&this.config.useHtml5){this.config.media=m.src;this.is_html5=true;this.$html=this.assembleHTML5(m.container,m.mimetype);a.extend(this,html5_methods);}else{if((this.config.media instanceof Array)&&(typeof this.config.media.push!=="undefined")){this.config.media=this.config.media[0];}this.$html=this.assembleHTML();}if(this.config.captions){this.getCaptions();}}return this.each(function(n){var p=a(this),o,m,l=function(q){if(q.$html.width()>580){q.$html.addClass("player-wide");}if(q.is_html5){q.player=document.getElementById(q.config.id);}};if(c.url.match(/^(http|https)\:\/\/www\.youtube\.com/)){o=new window.NOMENSA.player.YoutubePlayer(c);m=new window.NOMENSA.player.MediaplayerDecorator(o);m.onPlayerReady(function(){l(m);this.getPlayer().setLoop(true);});m.init(p);}else{m=new j(n);p.html(m.$html);l(m);window.NOMENSA.player.PlayerDaemon.addPlayer(m);}});};}(jQuery));
// Function.prototype.bind
//
// A polyfill for Function.prototype.bind. Which lets you bind a defined
// value to the `this` keyword in a function call.
//
// Bind is natively supported in:
//   IE9+
//   Chrome 7+
//   Firefox 4+
//   Safari 5.1.4+
//   iOS 6+
//   Android Browser 4+
//   Chrome for Android 0.16+
//
// Originally from:
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Function/bind
if (!Function.prototype.bind) {
  Function.prototype.bind = function (oThis) {
    if (typeof this !== "function") {
      // closest thing possible to the ECMAScript 5
      // internal IsCallable function
      throw new TypeError("Function.prototype.bind - what is trying to be bound is not callable");
    }

    var aArgs = Array.prototype.slice.call(arguments, 1),
        fToBind = this,
        fNOP = function () {},
        fBound = function () {
          return fToBind.apply(this instanceof fNOP && oThis
                 ? this
                 : oThis,
                 aArgs.concat(Array.prototype.slice.call(arguments)));
        };

    fNOP.prototype = this.prototype;
    fBound.prototype = new fNOP();

    return fBound;
  };
}

});
