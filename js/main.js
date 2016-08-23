$(window).load(function(){
	getData();
	search();	
	displayAllInfo(getParameterByName('uid'));	
}); //end

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

//search function
function search(){
	//search by name or phone
	$('#search').keyup(function() {//when key is pressed in search bar
	var searchTerm = $(this).val(); //val of search bar
	var myExp = new RegExp(searchTerm, "i"); //regular experation
	$.getJSON('data.json', function(data){//get the json file
		var output = "<ul id='result'>";
		$.each(data, function(key, val){
			if(((val.phone.search(myExp) != -1) || (val.firstName.search(myExp) != -1) || (val.lastName.search(myExp) != -1)) && searchTerm != ""){
				output += '<li>';
				output += '<a href="#" onclick="redirect('+val.userID+')">' +val.firstName+ ' '+val.lastName+'</a>';
				output += '</li>';
		   }
		});//end each
		output += "</ul>";
		$('#update').html(output);//output result to the update div
		});
	});	
}

//display all the info on profile page
function displayAllInfo(userID){
	//alert(userID);
	$.getJSON( "data.json", function( data ) {
		for (var i=0; i<=data.length; i++){
			if(data[i].userID == userID){
				$('.display').append('<tr class="name"><td><h2>'+data[i].firstName+' '+data[i].lastName+'</h2></td></tr>'+
					'<tr><td style="width:20%; ">Date of birth</td><td>'+data[i].DOB+'</td></tr>'+
					'<tr><td>Gender</td><td>'+data[i].gender+'</td></tr>'+
					'<tr><td>Phone</td><td>'+data[i].phone+'</td></tr>'+
					'<tr><td>Email</td><td>'+data[i].email+'</td></tr>'+
					'<tr><td>Location</td><td>'+data[i].location+'</td></tr>'+
					'<tr><td>Education</td><td>'+data[i].education+'</td></tr>'+
					'<tr><td>Previous employer</td><td>'+data[i].previous_employer+'</td></tr>'+
					'<tr><td>Previous role</td><td>'+data[i].previous_role+'</td></tr>'+
					'<tr><td>Work experience</td><td>'+data[i].work_experience+'</td></tr>'+
					'<tr><td>Skills</td><td>'+data[i].skills+'</td></tr>'+
					'<tr><td>Date applied</td><td>'+data[i].date_applied+'</td></tr>'+
					'<<tr><td>Notice period</td><td>'+data[i].notice_period+'</td></tr>'
				);
			}
		}
	});
}

//send the user to profile page
function redirect(userID){
	window.location.href = 'profile.html?uid='+userID;
}

//get userID from url
function getParameterByName(name, url) {
    if (!url) url = window.location.href;
    name = name.replace(/[\[\]]/g, "\\$&");
    var regex = new RegExp("[?&]" + name + "(=([^&#]*)|&|#|$)"),
        results = regex.exec(url);
    if (!results) return null;
    if (!results[2]) return '';
    return decodeURIComponent(results[2].replace(/\+/g, " "));
}