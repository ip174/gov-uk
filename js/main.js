$(window).load(function(){
	getData();
}); 

//get data from JSON
function getData(){
	//get and append data to table
	$.getJSON( "data.json", function( data ) {
		for (var i=0; i<=data.length; i++){		
			$("#applicants_tables tbody").append('<tr onclick="redirect('+data[i].userID+')"><td>'+data[i].firstName+
				'</td><td>'+data[i].lastName+
				'</td><td>'+data[i].email+
				'</td><td>'+data[i].phone+
				'</td><td>'+data[i].previous_role+
				'</td><td>'+data[i].date_applied+'</td></tr>'
			); 
		}
	});		
}

//send the user to profile page
function redirect(userID){
	window.location.href = 'profile.html?uid='+userID;
}
