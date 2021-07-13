// Start of server.js

class Server {

  constructor(ctx) {
    this.ctx = ctx;
    this._vars = {};
    this._types = {};
    this._commands = [ 'inputs',
                       'outputs',
                       'call',
                       'restore',
                       'store',
                       'free',
                       'clear',
                       'pause_profiling',
                       'unpause_profiling',
                       'report',
                       'rename'
                     ];
  }

  _get_arg(args, i) {
    if (i < args.length) {
      return args[i];
    } else {
      throw 'Insufficient command args';
    }
  }

  _get_entry_point(entry) {
    // TODO Context contains a list of entry points, my implementation does not
    // Seems to be a dictionary
    if (entry in this.ctx.get_entry_points()) {
      return this.ctx.get_entry_points()[entry];
    } else {
      throw "Unkown entry point: " + entry;
    }
  }


  _check_var(vname) {
    if (!(vname in this._vars)) {
      throw 'Unknown variable: ' + vname;
    }
  }

  _set_var(vname, v, t) {
    this._vars[vname] = v;
    this._types[vname] = t;
  }

  _get_type(vname) {
    this._check_var(vname);
    return this._types[vname];
  }

  _get_var(vname) {
    this._check_var(vname);
    return this._vars[vname];
  }

  _cmd_inputs(args) {
    var entry = this._get_arg(args, 0);
    var inputs = this._get_entry_point(entry)[0];
    for (var i = 0; i < inputs.length; i++) {
      console.log(inputs[i]);
    }
  }

  _cmd_outputs(args) {
    var entry = this._get_arg(args, 0);
    var outputs = this._get_entry_point(entry)[1];
    for (var i = 0; i < outputs.length; i++) {
      console.log(outputs[i]);
    }
  }

  _cmd_dummy(args) {
    // pass
  }

  _cmd_free(args) {
    for (var i = 0; i < args.length; i++) {
      var vname = args[i];
      this._check_var(vname);
      delete this._vars[vname];
    }
  }

  _cmd_rename(args) {
    var oldname = this._get_arg(args, 0)
    var newname = this._get_arg(args, 1)
    if (newname in this._vars) {
      throw "Variable already exists: " + newname;
    }
    this._vars[newname] = this._vars[oldname];
    this._types[newname] = this._types[oldname];
    delete this._vars[oldname];
    delete this._types[oldname];
  }

  _cmd_call(args) {
    var entry = this._get_entry_point(this._get_arg(args, 0));
    var num_ins = entry[0].length;
    var num_outs = entry[1].length;
    var expected_len = 1 + num_outs + num_ins

    if (args.length != expected_len) {
      throw "Invalid argument count, expected " + expected_len
    }

    var out_vnames = args.slice(1, num_outs+1)
    for (var i = 0; i < out_vnames.length; i++) {
      var out_vname = out_vnames[i];
      if (out_vname in this._vars) {
        throw "Variable already exists: " + out_vname;
      }
    }
    var in_vnames = args.slice(1+num_outs);
    var ins = [];
    for (var i = 0; i < in_vnames.length; i++) {
      ins.push(this._get_var(in_vnames[i]));
    }
    // Call entry point function from string name
    var vals = this.ctx[args[0]].apply(this.ctx, ins);
    if (num_outs == 1) {
      this._set_var(out_vnames[0], vals, entry[1][0]);
    } else {
      for (var i = 0; i < out_vnames.length; i++) {
        this._set_var(out_vnames[i], vals[i], entry[1][i]);
      }
    }
  }

  _cmd_store(args) {
    var fname = this._get_arg(args, 0);
    for (var i = 1; i < args.length; i++) {
      var vname = args[i];
      var value = this._get_var(vname);
      var typ = this._get_type(vname);

      //TODO right this more elengantly
      //TODO make sure file is open in binary mode
      var fs = require("fs");
      var bin_val = construct_binary_value(value, typ);
      fs.appendFileSync(fname, bin_val, 'binary')
    }
  }

  fut_to_dim_typ(typ) {
    var type = typ;
    var count = 0;
    while (type.substr(0, 2) == '[]') {
      count = count + 1;
      type = type.slice(2);
    }
    return [count, type];
  }

  _cmd_restore(args) {
    if (args.length % 2 == 0) {
      throw "Invalid argument count";
    }

    var fname = args[0];
    // TODO make sure this is legal
    var args = args.slice(1);

    // Reading from file is part of values.js
    ///////////////////////////////////////////
    //
    //    var fs = require("fs");
    //    fs.copyFile(fname, 'destination.txt', (err) => {
    //  if (err) throw err;
    //  console.log('source.txt was copied to destination.txt');
    //});
    ///////////////////////////////////////////
    var as = args;
    var reader = new Reader(fname);
    while (as.length != 0) {
      var vname = as[0];
      var typename = as[1];
      as = as.slice(2);

      if (vname in this._vars) {
        throw "Variable already exists: " + vname;
      }
      try {
        var value = read_value(typename, reader);
        if (typeof value == 'number' || typeof value == 'bigint') {
          this._set_var(vname, value, typename);
        } else {
          // We are working with an array and need to create to convert [shape, arr] to futhark ptr
          var shape= value[0];
          var arr = value[1];
          var dimtyp = this.fut_to_dim_typ(typename);
          var dim = dimtyp[0];
          var typ = dimtyp[1];
          var arg_list = [arr, ...shape];
          var fnam = "new_" + typ + "_" + dim + "d";
          var ptr = this.ctx[fnam].apply(this.ctx, arg_list);
          this._set_var(vname, ptr, typename);
        }
      } catch (err) {
        var err_msg = "Failed to restore variable " + vname + ".\nPossibly malformed data in " + fname + ".\n";
        throw "Failed to restore variable " + err_msg;
      }
    }
    skip_spaces(reader);
    if (reader.get_buff().length != 0) {
      throw "Expected EOF after reading values";
    }
  }

  _process_line(line) {
    // TODO make sure it splits on anywhite space
    var words = line.split(" ");
    if (words.length == 0) {
      throw "Empty line";
    } else {
      var cmd = words[0];
      var args = words.splice(1);
      if (this._commands.includes(cmd)) {
        switch (cmd) {
        case 'inputs': this._cmd_inputs(args); break;
        case 'outputs': this._cmd_outputs(args); break
        case 'call': this._cmd_call(args); break
        case 'restore': this._cmd_restore(args); break
        case 'store': this._cmd_store(args); break
        case 'free': this._cmd_free(args); break
        case 'clear': this._cmd_dummy(args); break
        case 'pause_profiling': this._cmd_dummy(args); break
        case 'unpause_profiling': this._cmd_dummy(args); break
        case 'report': this._cmd_dummy(args); break
        case 'rename': this._cmd_rename(args); break
        }
      } else {
        throw "Unknown command: " + cmd;
      }
    }
  }

  run() {
    console.log('%%% OK'); // TODO figure out if flushing is neccesary for JS
    const readline = require('readline');
    const rl = readline.createInterface(process.stdin);
    rl.on('line', (line) => {
      if (line == "") {
        rl.close();
      }
      try {
        this._process_line(line);
        console.log('%%% OK');
      } catch (err) {
        console.log('%%% FAILURE');
        console.log(err);
        console.log('%%% OK');
      }
    }).on('close', () => { process.exit(0); });
  }
}

// End of server.js
